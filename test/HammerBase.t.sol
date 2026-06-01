// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// Shared abstract base for the Hammer end-to-end domain test files: deploys and wires the full
// system, defines named actors, and provides funding helpers, shared constants, and an
// attestation kit. Domain test files inherit this.
//
// setUp() only deploys and wires; it calls no external protocol function. The SessionAuction
// implementation is deployed directly and locked by _disableInitializers in its constructor;
// initialize() is only ever called on clones, never on the implementation.

import {Test} from "forge-std/Test.sol";

import {SessionAuction} from "../src/SessionAuction.sol";
import {PaddleRegistry} from "../src/PaddleRegistry.sol";
import {FlagRegistry}   from "../src/FlagRegistry.sol";
import {Treasury}       from "../src/Treasury.sol";
import {AgentBond}      from "../src/AgentBond.sol";
import {Hammer}         from "../src/Hammer.sol";
import {MockERC20}      from "./mocks/MockERC20.sol";
import {Clones}         from "@openzeppelin/contracts/proxy/Clones.sol";

import {InitConfig, Ceiling, AttestationQuote} from "../src/types/HammerTypes.sol";

abstract contract HammerBase is Test {
    // Deployed system.
    Hammer         internal hammer;          // factory singleton (owns the impl)
    SessionAuction internal impl;            // SessionAuction implementation (locked)
    SessionAuction internal auction;         // session instance the domain tests drive
    PaddleRegistry internal paddles;
    FlagRegistry   internal flags;
    Treasury       internal treasury;
    AgentBond      internal operatorBond;    // concrete OperatorBond implementation
    MockERC20      internal token;           // 6-decimal ERC-20 rail (mirrors USDC)

    // Named actors.
    address internal seller;
    address internal bidder1;
    address internal bidder2;
    address internal bidder3;
    address internal arbiter;
    address internal settler;
    address internal ops;
    address internal operator1;              // TEE operator host 1
    address internal operator2;              // TEE operator host 2
    address internal pauser;
    address internal houseFeeRecipient;

    // Shared constants.
    bytes32 internal constant SESSION_ID = keccak256("HAMMER_E2E_SESSION");

    uint16  internal constant MIN_INCREMENT_BPS = 200;     // 2%
    uint16  internal constant FEE_BPS           = 250;     // 2.5%
    uint32  internal constant TIME_BUFFER_SEC   = 5 minutes;
    uint16  internal constant MAX_EXTENSIONS    = 10;
    uint32  internal constant AC_CHALLENGE_SEC  = 1 hours;
    uint32  internal constant SELLER_DELIVER_SEC = 7 days;
    uint32  internal constant DISPUTE_WINDOW_SEC = 3 days;
    uint128 internal constant DISPUTE_BOND_AMT   = 0.1 ether;
    uint128 internal constant INTEGRITY_BOND_AMT = 0.1 ether;
    uint32  internal constant INTEGRITY_TIMEOUT_SEC = 2 days;
    uint32  internal constant REVEAL_DEADLINE_SEC   = 1 hours;

    // Pinned TEE measurement values (test fixtures); bid blindness rests on these matching the
    // enclave that produced the attestation.
    bytes32 internal constant MR_ENCLAVE  = keccak256("MR_ENCLAVE_FIXTURE");
    bytes32 internal constant VENDOR_ROOT = keccak256("VENDOR_ROOT_FIXTURE");

    // default reserve + amounts (native rail; ERC-20 tests scale by token decimals)
    uint96  internal constant RESERVE_PRICE = 1 ether;
    uint256 internal constant INITIAL_ETH   = 1_000 ether;
    uint256 internal constant INITIAL_TOKEN = 1_000_000e6; // 1,000,000 units at 6 decimals

    // Attestation kit. A real secp256r1 operator keypair is seeded in setUp and folded into
    // _defaultInitConfig so domain tests can build a passing TEE attestation via _realQuote that
    // on-chain P256.verify accepts. P256_ORDER is the secp256r1 group order N; P256_HALF is N/2.
    // P256.verify rejects high-S signatures, so they must be low-S normalized (s <= N/2).
    uint256 internal constant P256_ORDER =
        0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551;
    uint256 internal constant P256_HALF =
        0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192a8;

    uint256 internal operatorPkBase; // operator secp256r1 private key
    bytes32 internal opQxBase;       // operator public key X (folded into _defaultInitConfig)
    bytes32 internal opQyBase;       // operator public key Y
    bytes32 internal opKeyIdBase;    // keccak256(abi.encode(qx, qy)); the registered operator keyId

    function setUp() public virtual {
        // actors
        seller            = makeAddr("seller");
        bidder1           = makeAddr("bidder1");
        bidder2           = makeAddr("bidder2");
        bidder3           = makeAddr("bidder3");
        arbiter           = makeAddr("arbiter");
        settler           = makeAddr("settler");
        ops               = makeAddr("ops");
        operator1         = makeAddr("operator1");
        operator2         = makeAddr("operator2");
        pauser            = makeAddr("pauser");
        houseFeeRecipient = makeAddr("houseFeeRecipient");

        // Seed the operator P-256 key folded into _defaultInitConfig. Private key must be in [1, N-1].
        operatorPkBase = _boundP256PkBase(uint256(keccak256("HAMMER_BASE_OPERATOR_P256_v1")));
        (uint256 oqx, uint256 oqy) = vm.publicKeyP256(operatorPkBase);
        opQxBase = bytes32(oqx);
        opQyBase = bytes32(oqy);
        opKeyIdBase = keccak256(abi.encode(opQxBase, opQyBase));

        // auxiliary registries and pools
        paddles      = new PaddleRegistry();
        flags        = new FlagRegistry();
        treasury     = new Treasury();
        operatorBond = new AgentBond();
        token        = new MockERC20("Mock USD", "mUSD", 6);

        // Implementation (locked by _disableInitializers in its constructor), the factory that owns
        // it, and a session clone the tests drive. initialize() is not called here.
        impl    = new SessionAuction();
        hammer  = new Hammer(address(impl));
        auction = SessionAuction(Clones.clone(address(impl)));

        // Authorize the factory on the Treasury and bond pools (so createSession could register a
        // clone in-tx), then register the session clone directly so its onlyAuction gates admit it.
        // Runs as the deployer, which owns both pools.
        treasury.setFactory(address(hammer));
        operatorBond.setFactory(address(hammer));
        operatorBond.setTreasury(address(treasury)); // AgentBond slash remainder flows to the Treasury
        treasury.registerClone(address(auction));
        operatorBond.registerClone(address(auction));

        // fund all actors on both rails
        _fundAll();
    }

    // Funding helpers.

    /// @notice Give an account native ETH (native payment rail).
    function fundEth(address account, uint256 amount) internal {
        vm.deal(account, amount);
    }

    /// @notice Mint MockERC20 to an account (ERC-20 payment rail).
    function fundToken(address account, uint256 amount) internal {
        token.mint(account, amount);
    }

    /// @notice Top every named actor up on both rails to the default starting balances.
    function _fundAll() internal {
        address[11] memory who = [
            seller, bidder1, bidder2, bidder3, arbiter, settler, ops,
            operator1, operator2, pauser, houseFeeRecipient
        ];
        for (uint256 i = 0; i < who.length; i++) {
            vm.deal(who[i], INITIAL_ETH);
            token.mint(who[i], INITIAL_TOKEN);
        }
    }

    // Config helper.

    /// @notice Build a default-valued InitConfig for `paymentToken` with one operator key pair.
    ///         Tests may override individual fields.
    function _defaultInitConfig(address paymentToken) internal view returns (InitConfig memory cfg) {
        bytes32[] memory qx = new bytes32[](1);
        bytes32[] memory qy = new bytes32[](1);
        qx[0] = opQxBase; // seeded on-curve P-256 key so attestations can P256.verify
        qy[0] = opQyBase;

        cfg = InitConfig({
            hammer: address(hammer),
            settler: settler,
            ops: ops,
            arbiter: arbiter,
            pauser: pauser,
            paddles: address(paddles),
            flags: address(flags),
            operatorBond: address(operatorBond),
            treasury: address(treasury),
            paymentToken: paymentToken,
            feeRecipient: houseFeeRecipient,
            sessionId: SESSION_ID,
            sessionStart: uint64(block.timestamp),
            sessionEnd: uint64(block.timestamp + 30 days),
            minIncrementBps: MIN_INCREMENT_BPS,
            feeBps: FEE_BPS,
            timeBufferSec: TIME_BUFFER_SEC,
            maxExtensions: MAX_EXTENSIONS,
            acChallengeSec: AC_CHALLENGE_SEC,
            sellerDeliverSec: SELLER_DELIVER_SEC,
            disputeWindowSec: DISPUTE_WINDOW_SEC,
            disputeBondAmt: DISPUTE_BOND_AMT,
            integrityBondAmt: INTEGRITY_BOND_AMT,
            integrityTimeoutSec: INTEGRITY_TIMEOUT_SEC,
            revealDeadlineSec: REVEAL_DEADLINE_SEC,
            mrEnclave: MR_ENCLAVE,
            vendorRoot: VENDOR_ROOT,
            operatorQx: qx,
            operatorQy: qy
        });
    }

    // Attestation kit helpers.

    /// @notice Bound a raw seed into the valid secp256r1 private-key range [1, N-1] (else signP256 /
    ///         publicKeyP256 revert).
    function _boundP256PkBase(uint256 seed) internal pure returns (uint256) {
        return (seed % (P256_ORDER - 1)) + 1;
    }

    /// @notice P-256 sign `digest` with `pk`, low-S normalized (s <= N/2) so P256.verify accepts it
    ///         (P256.sol rejects high-S).
    function _signP256LowSBase(uint256 pk, bytes32 digest) internal pure returns (bytes32 r, bytes32 s) {
        (r, s) = vm.signP256(pk, digest);

        if (uint256(s) > P256_HALF) {
            s = bytes32(P256_ORDER - uint256(s));
        }
    }

    /// @notice The seeded operator key's keyId, used as placeBid's `operatorKeyId` argument.
    function _baseOperatorKeyId() internal view returns (bytes32) {
        return opKeyIdBase;
    }

    /// @notice The canonical 10-field actionDigest the operator signs, byte-identical to the
    ///         preimage SessionAuction recomputes on-chain. Field order and types are load-bearing
    ///         for abi.encode: a reordered or short preimage yields a different digest and
    ///         P256.verify fails.
    function _actionDigestBase(
        Ceiling memory c,
        uint256 lotId,
        uint128 amount,
        uint64 bidIndex,
        AttestationQuote memory q
    ) internal pure returns (bytes32) {
        return keccak256(
            abi.encode(
                SESSION_ID,
                lotId,
                amount,
                c.nonceKey,
                bidIndex,
                c.ceilingCommit,
                q.nonce,
                q.mrEnclave,
                q.vendorRoot,
                q.observedPrevTop
            )
        );
    }

    /// @notice A measurement-correct quote carrying a real P-256 attestation by the seeded operator
    ///         key over the canonical digest of (c, lotId, amount, bidIndex, thisQuote). Two-pass:
    ///         assemble the signed-over fields, compute the digest, then fill r/s low-S normalized.
    function _realQuote(
        Ceiling memory c,
        uint256 lotId,
        uint128 amount,
        uint64 bidIndex,
        uint128 observedPrevTop,
        bytes32 nonce
    ) internal view returns (AttestationQuote memory q) {
        q = AttestationQuote({
            mrEnclave: MR_ENCLAVE,
            vendorRoot: VENDOR_ROOT,
            observedPrevTop: bytes32(uint256(observedPrevTop)),
            nonce: nonce,
            r: bytes32(0),
            s: bytes32(0)
        });

        bytes32 digest = _actionDigestBase(c, lotId, amount, bidIndex, q);
        (bytes32 r, bytes32 s) = _signP256LowSBase(operatorPkBase, digest);
        q.r = r;
        q.s = s;
    }
}
