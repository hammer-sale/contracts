// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// Blind-bidding tests for SessionAuction.placeBid: envelope authorization, TEE attestation
// verification, ceiling commitments, the three bidding strategies, and envelope revocation.
// Exercises ISessionAuction against a fresh clone of the locked implementation.
//
// Negative cases assert the exact revert selector (e.g. ISessionAuction.X.selector,
// Nonces.InvalidAccountNonce, Pausable.EnforcedPause) so a match cannot be an unrelated revert.
// Positive cases build a real P-256 attestation (vm.signP256 / vm.publicKeyP256 with low-S
// normalization) over the canonical 10-field digest plus a real EIP-712 ECDSA envelope, mock the
// KYC paddle, and pin the exact post-state and emitted events.
//
// Helper contracts in this file are B_-prefixed to avoid collisions with other domain files.

import {HammerBase} from "./HammerBase.t.sol";

import {Vm} from "forge-std/Vm.sol";

import {SessionAuction}  from "../src/SessionAuction.sol";
import {ISessionAuction} from "../src/interfaces/ISessionAuction.sol";

import {IPaddleRegistry} from "../src/interfaces/IPaddleRegistry.sol";

import {Pausable}  from "@openzeppelin/contracts/utils/Pausable.sol";
import {Nonces}    from "@openzeppelin/contracts/utils/Nonces.sol";
import {IERC1271}  from "@openzeppelin/contracts/interfaces/IERC1271.sol";
import {Clones}    from "@openzeppelin/contracts/proxy/Clones.sol";

import {
    Ceiling,
    AttestationQuote,
    InitConfig,
    Lot,
    Deposit,
    CEILING_TYPEHASH
} from "../src/types/HammerTypes.sol";

// File-level mock helpers, B_-prefixed to avoid collisions across domain files.

/// @dev Minimal ERC-1271 smart-wallet principal whose acceptance can be flipped mid-auction.
///      Returns the magic value 0x1626ba7e while `accept` is true, else a non-magic value.
contract B_MockERC1271Wallet is IERC1271 {
    bool public accept = true;

    function setAccept(bool v) external {
        accept = v;
    }

    function isValidSignature(bytes32, bytes calldata) external view returns (bytes4) {
        return accept ? IERC1271.isValidSignature.selector : bytes4(0xffffffff);
    }
}

contract B_BlindBiddingTest is HammerBase {
    // The clone is EIP712("Hammer","1") and its domain self-corrects to address(this), so a valid
    // envelope must be signed against verifyingContract == the called clone (here, `session`).
    bytes32 private constant EIP712_DOMAIN_TYPEHASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");
    bytes32 private constant HASHED_NAME = keccak256(bytes("Hammer"));
    bytes32 private constant HASHED_VERSION = keccak256(bytes("1"));

    // secp256r1 order N and its half. P256.verify rejects high-S (s > HALF_N), so the attestation
    // signer must low-S normalize (s = N - s).
    uint256 private constant P256_N =
        0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551;
    uint256 private constant P256_HALF_N =
        0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192a8;

    uint256 private constant LOT_ID = 1;

    // The session under test: a fresh clone of the locked implementation (not the HammerBase
    // `auction`, whose constructor ran _disableInitializers and so cannot be initialized). The
    // clone is unlocked, so initialize works, and its EIP-712 verifyingContract self-corrects to
    // address(session), which is what valid envelopes sign against.
    SessionAuction private session;

    // A real secp256r1 keypair so P256.verify passes. keyId is keccak256(abi.encode(qx, qy));
    // _initSession overrides the seeded init key with this one so registration matches.
    uint256 private operatorPk;
    bytes32 private opQx;
    bytes32 private opQy;
    bytes32 private opKeyId;

    // A second real operator key, for tests that two independent operator keys can each authorize.
    uint256 private operator2Pk;
    bytes32 private op2Qx;
    bytes32 private op2Qy;
    bytes32 private op2KeyId;

    // Key-bearing bidders: HammerBase actors are address-only, but EIP-712 signing needs private keys.
    address private alice;
    uint256 private alicePk;
    address private bob;
    uint256 private bobPk;

    // The KYC paddles the registry is mocked to return (nonzero == registered).
    uint16 private constant PADDLE_ALICE = 11;
    uint16 private constant PADDLE_BOB = 22;

    function setUp() public override {
        super.setUp();

        // Private keys must be in [1, N-1] for secp256r1, else signP256 / publicKeyP256 revert.
        operatorPk = _boundP256Pk(uint256(keccak256("B_OPERATOR_P256_PK_v1")));
        (uint256 qx, uint256 qy) = vm.publicKeyP256(operatorPk);
        opQx = bytes32(qx);
        opQy = bytes32(qy);
        opKeyId = keccak256(abi.encode(opQx, opQy));

        // A second independent operator key, for tests that any 1-of-N key can authorize.
        operator2Pk = _boundP256Pk(uint256(keccak256("B_OPERATOR2_P256_PK_v1")));
        (uint256 q2x, uint256 q2y) = vm.publicKeyP256(operator2Pk);
        op2Qx = bytes32(q2x);
        op2Qy = bytes32(q2y);
        op2KeyId = keccak256(abi.encode(op2Qx, op2Qy));

        // HammerBase actors are address-only; EIP-712 signing needs the private keys too.
        (alice, alicePk) = makeAddrAndKey("B_alice");
        (bob, bobPk) = makeAddrAndKey("B_bob");
        fundEth(alice, INITIAL_ETH);
        fundEth(bob, INITIAL_ETH);
    }

    // Pre-state helpers (private; all go through the real entrypoints).

    /// @dev Initialize a fresh unlocked clone for `paymentToken`, seeding the real operator key
    ///      (so opKeyId is active and P256.verify can pass). cfg.hammer is the factory address, so
    ///      onlyHammer paths prank it.
    function _initSession(address paymentToken) private {
        session = SessionAuction(Clones.clone(address(impl)));

        InitConfig memory cfg = _defaultInitConfig(paymentToken);
        cfg.operatorQx[0] = opQx; // override the fixture key with a real, on-curve P-256 key
        cfg.operatorQy[0] = opQy;

        vm.prank(address(hammer));
        session.initialize(cfg);
    }

    /// @dev Variant seeding an off-curve fixture key, to test that P256.verify fails closed.
    function _initSessionOffCurve(address paymentToken) private {
        session = SessionAuction(Clones.clone(address(impl)));

        InitConfig memory cfg = _defaultInitConfig(paymentToken);
        cfg.operatorQx[0] = keccak256("OPERATOR_QX_FIXTURE"); // keccak bytes: off-curve with overwhelming odds
        cfg.operatorQy[0] = keccak256("OPERATOR_QY_FIXTURE");

        vm.prank(address(hammer));
        session.initialize(cfg);
    }

    /// @dev Open LOT_ID with a far endsAt so timing never trips unless a test warps.
    function _openLot() private {
        _openLot(uint64(block.timestamp + 1 days));
    }

    function _openLot(uint64 endsAt) private {
        vm.prank(address(hammer));
        session.openLot(LOT_ID, seller, RESERVE_PRICE, endsAt);
    }

    /// @dev Mock a nonzero paddle for `principal` so the KYC gate (paddleOf==0 -> Unauthorized)
    ///      passes; the registry otherwise returns 0.
    function _mockPaddle(address principal, uint16 paddleId) private {
        vm.mockCall(
            address(paddles),
            abi.encodeWithSelector(IPaddleRegistry.paddleOf.selector, principal),
            abi.encode(paddleId)
        );
    }

    /// @dev Fund `principal`'s free deposit on the native rail (deposit > ceiling so slack hides it).
    function _depositNative(address principal, uint256 amount) private {
        vm.prank(principal);
        session.depositCeiling{value: amount}(LOT_ID, amount);
    }

    /// @dev The keyed nonceKey the envelope must carry: keccak256(sessionId, lotId, principal)
    ///      truncated to uint192. placeBid rejects any other value with BadNonceKey.
    function _nonceKey(uint256 lotId, address principal) private pure returns (uint192) {
        return uint192(uint256(keccak256(abi.encode(SESSION_ID, lotId, principal))));
    }

    /// @dev The packed keyed-nonce OZ reverts with on a keyed replay/out-of-order. For a non-zero
    ///      key the revert is InvalidAccountNonce(owner, _pack(key, n)) where
    ///      _pack(key, n) == (uint256(key) << 64) | n, not the bare nonce n. Derived from the live
    ///      nonceKey so it tracks the envelope under test.
    function _packedNonce(uint256 lotId, address principal, uint64 n) private pure returns (uint256) {
        return (uint256(_nonceKey(lotId, principal)) << 64) | uint256(n);
    }

    /// @dev The commitment exactly as the client/contract builds it (abi.encode, NOT packed).
    function _commit(uint128 maxBid, bytes32 salt) private pure returns (bytes32) {
        return keccak256(abi.encode(maxBid, salt));
    }

    /// @dev A well-formed envelope for `principal` committing (maxBid, salt) under `strategy`.
    function _ceiling(address principal, uint128 maxBid, bytes32 salt, uint8 strategy)
        private
        view
        returns (Ceiling memory c)
    {
        c = Ceiling({
            principal: principal,
            sessionId: SESSION_ID,
            lotId: LOT_ID,
            ceilingCommit: _commit(maxBid, salt),
            strategy: strategy,
            deadline: uint64(block.timestamp + 7 days),
            maxBids: uint64(MAX_EXTENSIONS) + 8,
            nonceKey: _nonceKey(LOT_ID, principal)
        });
    }

    /// @dev EIP-712 domain separator for clone `a` (self-corrected to its address).
    function _domainSeparator(address a) private view returns (bytes32) {
        return keccak256(abi.encode(EIP712_DOMAIN_TYPEHASH, HASHED_NAME, HASHED_VERSION, block.chainid, a));
    }

    /// @dev The EIP-712 struct hash of a Ceiling (the 8-field CEILING_TYPEHASH preimage).
    function _ceilingStructHash(Ceiling memory c) private pure returns (bytes32) {
        return keccak256(
            abi.encode(
                CEILING_TYPEHASH,
                c.principal,
                c.sessionId,
                c.lotId,
                c.ceilingCommit,
                c.strategy,
                c.deadline,
                c.maxBids,
                c.nonceKey
            )
        );
    }

    /// @dev Sign a Ceiling with ECDSA (`pk`) against clone `a`'s self-correcting domain.
    function _signCeiling(address a, uint256 pk, Ceiling memory c) private view returns (bytes memory) {
        bytes32 digest = keccak256(abi.encodePacked("\x19\x01", _domainSeparator(a), _ceilingStructHash(c)));
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(pk, digest);
        return abi.encodePacked(r, s, v);
    }

    /// @dev The canonical 10-field action digest the enclave signs and the contract recomputes.
    ///      Field types are load-bearing for abi.encode: SESSION_ID bytes32, lotId uint256, amount
    ///      uint128, nonceKey uint192, bidIndex uint64, then five bytes32. A reordered or short
    ///      preimage yields a different digest, so P256.verify fails.
    function _actionDigest(
        Ceiling memory c,
        uint256 lotId,
        uint128 amount,
        uint64 bidIndex,
        AttestationQuote memory q
    ) private pure returns (bytes32) {
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

    /// @dev Bound a raw seed into the valid secp256r1 private-key range [1, N-1].
    function _boundP256Pk(uint256 seed) private pure returns (uint256) {
        return (seed % (P256_N - 1)) + 1;
    }

    /// @dev P-256 sign `digest` with `pk`, low-S normalized to satisfy P256.verify (s <= HALF_N).
    function _signP256LowS(uint256 pk, bytes32 digest) private pure returns (bytes32 r, bytes32 s) {
        (r, s) = vm.signP256(pk, digest);

        if (uint256(s) > P256_HALF_N) {
            s = bytes32(P256_N - uint256(s)); // flip s to the low half
        }
    }

    /// @dev A measurement-correct quote whose r/s is a real P-256 attestation by `signerPk` over
    ///      the canonical digest of (c, lotId, amount, bidIndex, this quote): fill the signed
    ///      fields, compute the digest, then write r/s back in.
    function _quote(
        Ceiling memory c,
        uint128 amount,
        uint64 bidIndex,
        uint128 observedPrevTop,
        bytes32 nonce,
        uint256 signerPk
    ) private pure returns (AttestationQuote memory q) {
        q = AttestationQuote({
            mrEnclave: MR_ENCLAVE,
            vendorRoot: VENDOR_ROOT,
            observedPrevTop: bytes32(uint256(observedPrevTop)),
            nonce: nonce,
            r: bytes32(0),
            s: bytes32(0)
        });

        bytes32 digest = _actionDigest(c, LOT_ID, amount, bidIndex, q);
        (bytes32 r, bytes32 s) = _signP256LowS(signerPk, digest);
        q.r = r;
        q.s = s;
    }

    /// @dev Deterministic per-(test, leg) quote nonce so independent bids never collide.
    function _qnonce(string memory tag, uint64 bidIndex) private pure returns (bytes32) {
        return keccak256(abi.encode("B_QUOTE_NONCE", tag, bidIndex));
    }

    /// @dev Place a fully valid attested bid for `principal` (KYC mocked, deposit funded). Returns
    ///      the envelope so callers can reuse its nonceKey. `signerPk`/`keyId` select the operator.
    function _placeValidBid(
        address principal,
        uint256 pk,
        uint16 paddleId,
        uint128 maxBid,
        bytes32 salt,
        uint8 strategy,
        uint64 bidIndex,
        uint128 amount,
        uint128 observedPrevTop,
        bytes32 quoteNonce,
        uint256 signerPk,
        bytes32 keyId,
        address relayer
    ) private returns (Ceiling memory c) {
        _mockPaddle(principal, paddleId);

        c = _ceiling(principal, maxBid, salt, strategy);
        bytes memory sig = _signCeiling(address(session), pk, c);
        AttestationQuote memory q = _quote(c, amount, bidIndex, observedPrevTop, quoteNonce, signerPk);

        vm.prank(relayer);
        session.placeBid(c, LOT_ID, principal, bidIndex, amount, sig, keyId, q);
    }

    // Relayer-agnostic authorization: a bid is bound to the signed principal, not the sender.

    /// @dev placeBid is authorized by the signature over the explicit principal arg, not by
    ///      msg.sender. Submitted from an arbitrary relayer it sets lot.highBidder == principal;
    ///      a second run that changes only msg.sender yields the identical outcome.
    function test_PlaceBidRelayerAgnostic() public {
        _initSession(address(0));
        _openLot();

        uint128 amount = uint128(RESERVE_PRICE);
        _depositNative(alice, 10 ether);

        // Relayer #1 is bidder3 (a third party, not alice, not an operator address).
        address relayer1 = bidder3;
        _placeValidBid(
            alice, alicePk, PADDLE_ALICE, 5 ether, keccak256("B01-salt"), 0, 0, amount, 0,
            _qnonce("B01a", 0), operatorPk, opKeyId, relayer1
        );

        Lot memory lot = session.getLot(LOT_ID);
        assertEq(lot.highBidder, alice, "highBidder is the principal, never the relayer");
        assertTrue(lot.highBidder != relayer1, "highBidder is not the relayer");
        assertEq(lot.highBid, amount, "top bid recorded");
        assertEq(uint256(lot.winnerSeq), 1, "first bid is seq 1");

        // Re-run on a FRESH lot changing ONLY msg.sender (relayer2 != relayer1): identical outcome.
        uint256 lot2 = 2;
        vm.prank(address(hammer));
        session.openLot(lot2, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));

        _mockPaddle(bob, PADDLE_BOB);

        vm.prank(bob);
        session.depositCeiling{value: 10 ether}(lot2, 10 ether);

        Ceiling memory c2 = Ceiling({
            principal: bob,
            sessionId: SESSION_ID,
            lotId: lot2,
            ceilingCommit: _commit(5 ether, keccak256("B01-salt2")),
            strategy: 0,
            deadline: uint64(block.timestamp + 7 days),
            maxBids: uint64(MAX_EXTENSIONS) + 8,
            nonceKey: _nonceKey(lot2, bob)
        });
        bytes memory sig2 = _signCeiling(address(session), bobPk, c2);

        AttestationQuote memory q2 = AttestationQuote({
            mrEnclave: MR_ENCLAVE,
            vendorRoot: VENDOR_ROOT,
            observedPrevTop: bytes32(uint256(0)),
            nonce: _qnonce("B01b", 0),
            r: bytes32(0),
            s: bytes32(0)
        });
        bytes32 d2 = keccak256(
            abi.encode(
                SESSION_ID, lot2, amount, c2.nonceKey, uint64(0),
                c2.ceilingCommit, q2.nonce, q2.mrEnclave, q2.vendorRoot, q2.observedPrevTop
            )
        );
        (q2.r, q2.s) = _signP256LowS(operatorPk, d2);

        address relayer2 = settler; // a DIFFERENT msg.sender

        vm.prank(relayer2);
        session.placeBid(c2, lot2, bob, 0, amount, sig2, opKeyId, q2);

        Lot memory lotB = session.getLot(lot2);
        assertEq(lotB.highBidder, bob, "outcome depends on the signed principal, not msg.sender");
        assertTrue(lotB.highBidder != relayer2, "highBidder still not the relayer");
    }

    // Envelope field-mismatch / signature-failure matrix. Each sub-case flips exactly one binding
    // of an otherwise-valid envelope and asserts the matching selector; a final fund-conservation +
    // nonce-survival check proves every revert happened before the nonce was consumed (a fresh valid
    // bid at bidIndex 0 still succeeds).
    function test_RevertWhen_AuthorizeBidFieldMismatch() public {
        _initSession(address(0));
        _openLot();
        _mockPaddle(alice, PADDLE_ALICE);
        _depositNative(alice, 10 ether);

        uint128 amount = uint128(RESERVE_PRICE);
        uint128 maxBid = 5 ether;
        bytes32 salt = keccak256("B02-salt");

        // (a) c.principal != principal -> Unauthorized. Sign over the mutated envelope so the
        //     failure is the principal binding, not the signature.
        {
            Ceiling memory c = _ceiling(alice, maxBid, salt, 0);
            c.principal = bob; // mismatch vs the principal arg (alice)
            bytes memory sig = _signCeiling(address(session), bobPk, c);
            AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B02a", 0), operatorPk);

            vm.prank(alice);
            vm.expectRevert(ISessionAuction.Unauthorized.selector);
            session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
        }

        // (b) c.sessionId != SESSION_ID -> WrongSession.
        {
            Ceiling memory c = _ceiling(alice, maxBid, salt, 0);
            c.sessionId = keccak256("WRONG_SESSION");
            bytes memory sig = _signCeiling(address(session), alicePk, c);
            AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B02b", 0), operatorPk);

            vm.prank(alice);
            vm.expectRevert(ISessionAuction.WrongSession.selector);
            session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
        }

        // (c) c.lotId != lotId (cross-lot replay) -> WrongLot.
        {
            Ceiling memory c = _ceiling(alice, maxBid, salt, 0);
            c.lotId = LOT_ID + 99;
            bytes memory sig = _signCeiling(address(session), alicePk, c);
            AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B02c", 0), operatorPk);

            vm.prank(alice);
            vm.expectRevert(ISessionAuction.WrongLot.selector);
            session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
        }

        // (d) block.timestamp > c.deadline -> EnvelopeExpired.
        {
            Ceiling memory c = _ceiling(alice, maxBid, salt, 0);
            c.deadline = uint64(block.timestamp - 1); // already expired
            bytes memory sig = _signCeiling(address(session), alicePk, c);
            AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B02d", 0), operatorPk);

            vm.prank(alice);
            vm.expectRevert(ISessionAuction.EnvelopeExpired.selector);
            session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
        }

        // (e) c.nonceKey != keccak192(sessionId, lotId, principal) -> BadNonceKey.
        {
            Ceiling memory c = _ceiling(alice, maxBid, salt, 0);
            c.nonceKey = c.nonceKey ^ uint192(1); // any wrong key
            bytes memory sig = _signCeiling(address(session), alicePk, c);
            AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B02e", 0), operatorPk);

            vm.prank(alice);
            vm.expectRevert(ISessionAuction.BadNonceKey.selector);
            session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
        }

        // (f) envelopeCancelled[principal][nonceKey] == true -> EnvelopeRevoked. Run on bob, not
        //     alice, so alice's LOT_ID key stays un-revoked for the survival bid below. The
        //     revocation check precedes the nonce/KYC/deposit steps, so bob needs no paddle or deposit.
        {
            Ceiling memory c = _ceiling(bob, maxBid, salt, 0);
            bytes memory sig = _signCeiling(address(session), bobPk, c);
            AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B02f", 0), operatorPk);

            vm.prank(bob);
            session.cancelEnvelope(c.nonceKey); // bob revokes bob's key

            vm.prank(bob);
            vm.expectRevert(ISessionAuction.EnvelopeRevoked.selector);
            session.placeBid(c, LOT_ID, bob, 0, amount, sig, opKeyId, q);
        }

        // (g) wrong signing key -> BadSignature. Sign with bob over alice's envelope: the principal
        //     binding passes, but SignatureChecker recovers bob, not alice, so the digest check fails.
        {
            Ceiling memory c = _ceiling(alice, maxBid, salt, 0);
            bytes memory badSig = _signCeiling(address(session), bobPk, c); // not alice's key
            AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B02g", 0), operatorPk);

            vm.prank(alice);
            vm.expectRevert(ISessionAuction.BadSignature.selector);
            session.placeBid(c, LOT_ID, alice, 0, amount, badSig, opKeyId, q);
        }

        // Nonce-survival control: none of (a)-(e),(g) consumed alice's bidIndex 0 on the LOT_ID
        // key or moved her escrow, and (f) cancelled only bob's key, so a fresh valid bid at
        // bidIndex 0 on that same key must still succeed, proving every revert fired before the
        // nonce was consumed on the exact key the reverts targeted.
        Deposit memory before = _deposit(alice);
        assertEq(before.committed, 0, "no escrow committed by any reverted attempt");

        Ceiling memory cOk = _ceiling(alice, maxBid, salt, 0); // alice, LOT_ID, canonical nonceKey
        bytes memory sigOk = _signCeiling(address(session), alicePk, cOk);
        AttestationQuote memory qOk = _quote(cOk, amount, 0, 0, _qnonce("B02ok", 0), operatorPk);

        vm.prank(alice);
        session.placeBid(cOk, LOT_ID, alice, 0, amount, sigOk, opKeyId, qOk);

        Lot memory landed = session.getLot(LOT_ID);
        assertEq(landed.highBidder, alice, "original-key bidIndex 0 still works post-revert");
        assertEq(uint256(landed.winnerSeq), 1, "the surviving bid is the FIRST consumed index on the key");
        assertEq(landed.highBid, amount, "the surviving bid landed at the expected amount");

        // A second valid bid now requires bidIndex 1 (the key advanced exactly once), confirming
        // only one nonce was burned across the whole matrix.
        uint128 amount2 = amount + uint128((uint256(amount) * MIN_INCREMENT_BPS) / 10_000) + 1;
        AttestationQuote memory qOk2 = _quote(cOk, amount2, 1, amount, _qnonce("B02ok", 1), operatorPk);

        vm.prank(alice);
        session.placeBid(cOk, LOT_ID, alice, 1, amount2, sigOk, opKeyId, qOk2);
        assertEq(uint256(session.getLot(LOT_ID).winnerSeq), 2, "key advances to index 1 (only one prior burn)");
    }

    // SignatureChecker: EOA vs ERC-1271 vs EIP-7702.

    /// @dev A 7702-delegated EOA has 23 bytes of code (0xef0100 || addr), so SignatureChecker
    ///      routes to ERC-1271, NOT ECDSA; a plain ECDSA sig then fails -> BadSignature.
    function test_RevertWhen_EIP7702PlainECDSA() public {
        _initSession(address(0));
        _openLot();

        // alice gains a 7702 designation: code.length == 23, so signer.code.length != 0 routes to
        // the ERC-1271 staticcall, which on a designation pointing at a non-1271 target fails.
        bytes memory designation = abi.encodePacked(hex"ef0100", address(0xBEEF));
        vm.etch(alice, designation);
        assertEq(alice.code.length, 23, "7702 designation is 23 bytes");

        _mockPaddle(alice, PADDLE_ALICE);
        _depositNative(alice, 10 ether);

        uint128 amount = uint128(RESERVE_PRICE);
        Ceiling memory c = _ceiling(alice, 5 ether, keccak256("B03b-salt"), 0);
        bytes memory plainEcdsa = _signCeiling(address(session), alicePk, c); // plain ECDSA
        AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B03b", 0), operatorPk);

        // Plain ECDSA routed through the ERC-1271 staticcall -> BadSignature.
        vm.prank(alice);
        vm.expectRevert(ISessionAuction.BadSignature.selector);
        session.placeBid(c, LOT_ID, alice, 0, amount, plainEcdsa, opKeyId, q);
    }

    /// @dev An ERC-1271 principal accepts a valid contract sig (lands), then rotates its signer to
    ///      reject so a later bid reverts BadSignature, while the earlier landed bid's state
    ///      persists. The rotation only costs the principal its own later bids, never a third party.
    function test_RevertWhen_ERC1271SignerRotated() public {
        _initSession(address(0));
        _openLot();

        B_MockERC1271Wallet wallet = new B_MockERC1271Wallet(); // accepts by default (0x1626ba7e)
        address principal = address(wallet);
        _mockPaddle(principal, PADDLE_ALICE);

        fundEth(principal, 20 ether);

        vm.prank(principal);
        session.depositCeiling{value: 15 ether}(LOT_ID, 15 ether);

        // Bid #1 (bidIndex 0) lands: ERC-1271 returns the magic value, so any non-empty sig passes.
        uint128 amount1 = uint128(RESERVE_PRICE);
        Ceiling memory c1 = _ceiling(principal, 10 ether, keccak256("B03c-salt"), 0);
        bytes memory sig1 = hex"01"; // opaque; the 1271 wallet accepts unconditionally
        AttestationQuote memory q1 = _quote(c1, amount1, 0, 0, _qnonce("B03c", 0), operatorPk);

        vm.prank(bidder3); // relayer-agnostic
        session.placeBid(c1, LOT_ID, principal, 0, amount1, sig1, opKeyId, q1);

        Lot memory afterFirst = session.getLot(LOT_ID);
        assertEq(afterFirst.highBidder, principal, "ERC-1271 principal landed bid 1");
        assertEq(afterFirst.highBid, amount1, "bid 1 amount recorded");

        // Rotate the signer to REJECT; bid #2 (bidIndex 1) must revert BadSignature.
        wallet.setAccept(false);
        uint128 amount2 = uint128(RESERVE_PRICE) + uint128(RESERVE_PRICE) / 10; // strictly higher
        Ceiling memory c2 = _ceiling(principal, 10 ether, keccak256("B03c-salt"), 0);
        bytes memory sig2 = hex"02";
        AttestationQuote memory q2 = _quote(c2, amount2, 1, amount1, _qnonce("B03c", 1), operatorPk);

        vm.prank(bidder3);
        vm.expectRevert(ISessionAuction.BadSignature.selector);
        session.placeBid(c2, LOT_ID, principal, 1, amount2, sig2, opKeyId, q2);

        // The earlier landed bid is unaffected by the later signer rotation.
        Lot memory afterReject = session.getLot(LOT_ID);
        assertEq(afterReject.highBidder, principal, "earlier landed bid persists after rotation");
        assertEq(afterReject.highBid, amount1, "top still bid 1");
    }

    // EIP-712 domain self-corrects to the clone.

    /// @dev A signature against the correct clone domain (verifyingContract == address(session))
    ///      validates; a signature against the factory address or a wrong chainId reverts
    ///      BadSignature. This closes cross-chain and cross-contract replay.
    function test_EIP712DomainSelfCorrectsOnClone() public {
        _initSession(address(0));
        _openLot();
        _mockPaddle(alice, PADDLE_ALICE);
        _depositNative(alice, 10 ether);

        uint128 amount = uint128(RESERVE_PRICE);
        Ceiling memory c = _ceiling(alice, 5 ether, keccak256("B04-salt"), 0);
        AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B04", 0), operatorPk);
        bytes32 structHash = _ceilingStructHash(c);

        // (a) Wrong verifyingContract = the factory address -> BadSignature.
        {
            bytes32 wrongDomain = keccak256(
                abi.encode(EIP712_DOMAIN_TYPEHASH, HASHED_NAME, HASHED_VERSION, block.chainid, address(hammer))
            );
            bytes32 digest = keccak256(abi.encodePacked("\x19\x01", wrongDomain, structHash));
            (uint8 v, bytes32 r, bytes32 s) = vm.sign(alicePk, digest);
            bytes memory badSig = abi.encodePacked(r, s, v);

            vm.prank(alice);
            vm.expectRevert(ISessionAuction.BadSignature.selector);
            session.placeBid(c, LOT_ID, alice, 0, amount, badSig, opKeyId, q);
        }

        // (b) Wrong chainId domain -> BadSignature.
        {
            bytes32 wrongChainDomain = keccak256(
                abi.encode(EIP712_DOMAIN_TYPEHASH, HASHED_NAME, HASHED_VERSION, block.chainid + 1, address(session))
            );
            bytes32 digest = keccak256(abi.encodePacked("\x19\x01", wrongChainDomain, structHash));
            (uint8 v, bytes32 r, bytes32 s) = vm.sign(alicePk, digest);
            bytes memory badSig = abi.encodePacked(r, s, v);

            vm.prank(alice);
            vm.expectRevert(ISessionAuction.BadSignature.selector);
            session.placeBid(c, LOT_ID, alice, 0, amount, badSig, opKeyId, q);
        }

        // (c) The correct clone-domain signature validates and the bid lands. Fresh quote nonce
        //     (the prior reverted attempts never consumed one).
        {
            bytes memory goodSig = _signCeiling(address(session), alicePk, c);
            AttestationQuote memory qOk = _quote(c, amount, 0, 0, _qnonce("B04ok", 0), operatorPk);

            vm.prank(alice);
            session.placeBid(c, LOT_ID, alice, 0, amount, goodSig, opKeyId, qOk);
            assertEq(session.getLot(LOT_ID).highBidder, alice, "correct-clone-domain sig validates");
        }
    }

    // Keyed-nonce ladder: strict monotonic per-key bid indices.

    /// @dev Replay of bidIndex 0 reverts InvalidAccountNonce(principal, current) where current is
    ///      the packed next-expected nonce (uint256(nonceKey) << 64) | 1, not the bare 1: the
    ///      nonceKey is non-zero, so OZ takes the keyed branch. There is no uint256 keyedNonce
    ///      calldata field; the index travels as bidIndex.
    function test_RevertWhen_BidIndexReplayed() public {
        _initSession(address(0));
        _openLot();
        _depositNative(alice, 20 ether);

        // First bid consumes bidIndex 0.
        Ceiling memory c = _placeValidBid(
            alice, alicePk, PADDLE_ALICE, 10 ether, keccak256("B05r-salt"), 0, 0,
            uint128(RESERVE_PRICE), 0, _qnonce("B05r", 0), operatorPk, opKeyId, alice
        );

        // Replay bidIndex 0: the keyed nonce is now 1, so re-using 0 reverts InvalidAccountNonce
        // with the packed next-expected value.
        bytes memory sig = _signCeiling(address(session), alicePk, c);
        AttestationQuote memory q = _quote(c, uint128(RESERVE_PRICE), 0, 0, _qnonce("B05r2", 0), operatorPk);

        vm.prank(alice);
        vm.expectRevert(
            abi.encodeWithSelector(Nonces.InvalidAccountNonce.selector, alice, _packedNonce(LOT_ID, alice, 1))
        );
        session.placeBid(c, LOT_ID, alice, 0, uint128(RESERVE_PRICE), sig, opKeyId, q);
    }

    /// @dev Out-of-order index (skip from 0 to 2 before consuming 1) reverts InvalidAccountNonce
    ///      with current == the packed next-expected index (uint256(nonceKey) << 64) | 1, proving
    ///      strict monotonicity.
    function test_RevertWhen_BidIndexOutOfOrder() public {
        _initSession(address(0));
        _openLot();
        _depositNative(alice, 20 ether);

        // Consume bidIndex 0.
        _placeValidBid(
            alice, alicePk, PADDLE_ALICE, 10 ether, keccak256("B05o-salt"), 0, 0,
            uint128(RESERVE_PRICE), 0, _qnonce("B05o", 0), operatorPk, opKeyId, alice
        );

        // Jump to bidIndex 2 (skipping 1) -> InvalidAccountNonce with the packed next-expected index.
        uint128 amount2 = uint128(RESERVE_PRICE) + uint128(RESERVE_PRICE) / 10;
        Ceiling memory c = _ceiling(alice, 10 ether, keccak256("B05o-salt"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);
        AttestationQuote memory q = _quote(c, amount2, 2, uint128(RESERVE_PRICE), _qnonce("B05o", 2), operatorPk);

        vm.prank(alice);
        vm.expectRevert(
            abi.encodeWithSelector(Nonces.InvalidAccountNonce.selector, alice, _packedNonce(LOT_ID, alice, 1))
        );
        session.placeBid(c, LOT_ID, alice, 2, amount2, sig, opKeyId, q);
    }

    // UnknownOperator: an unregistered or revoked operator key fails closed.

    /// @dev An operatorKeyId that was never registered reverts UnknownOperator, and it is the first
    ///      attestation check: even with garbage r/s the revert is UnknownOperator (not
    ///      BadAttestationSig), so P256.verify is never reached. Records logs across the revert and
    ///      pins the empty top + alice's full free, so no partial emit/commit precedes the guard.
    function test_RevertWhen_UnknownOperator() public {
        _initSession(address(0));
        _openLot();
        _mockPaddle(alice, PADDLE_ALICE);
        uint256 funded = 10 ether;
        _depositNative(alice, funded);

        // Fresh lot: the no-partial-commit baseline is the empty top.
        assertEq(uint256(session.getLot(LOT_ID).winnerSeq), 0, "no bid yet (winnerSeq 0)");
        assertEq(session.getLot(LOT_ID).highBidder, address(0), "no top bidder yet");
        assertEq(session.withdrawableFree(LOT_ID, alice), funded, "full deposit free, nothing committed");

        uint128 amount = uint128(RESERVE_PRICE);
        Ceiling memory c = _ceiling(alice, 5 ether, keccak256("B06-salt"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);

        // Garbage r/s under an unregistered key: UnknownOperator must fire before P256.verify.
        AttestationQuote memory q = AttestationQuote({
            mrEnclave: MR_ENCLAVE,
            vendorRoot: VENDOR_ROOT,
            observedPrevTop: bytes32(uint256(0)),
            nonce: _qnonce("B06", 0),
            r: bytes32(uint256(123456)),
            s: bytes32(uint256(654321))
        });
        bytes32 unknownKeyId = keccak256(abi.encode(keccak256("NEVER"), keccak256("REGISTERED")));

        vm.recordLogs();
        vm.prank(alice);
        vm.expectRevert(ISessionAuction.UnknownOperator.selector);
        session.placeBid(c, LOT_ID, alice, 0, amount, sig, unknownKeyId, q);
        _assertNoBidEvents(vm.getRecordedLogs());

        // No partial commit on the unregistered-key reject path: no top, no escrow moved.
        Lot memory lot = session.getLot(LOT_ID);
        assertEq(uint256(lot.winnerSeq), 0, "winnerSeq did NOT advance on an unknown-operator reject");
        assertEq(lot.highBidder, address(0), "no top recorded on an unknown-operator reject");
        assertEq(lot.highBid, 0, "no top amount recorded on an unknown-operator reject");
        assertEq(session.withdrawableFree(LOT_ID, alice), funded, "alice free == full deposit (no spurious commit)");
    }

    /// @dev A key that was registered, used, then revoked reverts UnknownOperator at the next bid.
    function test_RevokedKeyRejectedAtPlaceBid() public {
        _initSession(address(0));
        _openLot();

        // The seeded key is active; keyId is the canonical keccak256(abi.encode(qx, qy)).
        assertEq(opKeyId, keccak256(abi.encode(opQx, opQy)), "keyId == keccak256(abi.encode(qx,qy))");
        assertTrue(session.isOperatorActive(opKeyId), "seeded operator key active");

        // A bid under the active key verifies (lands).
        _depositNative(alice, 20 ether);
        _placeValidBid(
            alice, alicePk, PADDLE_ALICE, 10 ether, keccak256("B22-salt"), 0, 0,
            uint128(RESERVE_PRICE), 0, _qnonce("B22", 0), operatorPk, opKeyId, alice
        );
        assertEq(session.getLot(LOT_ID).highBidder, alice, "active-key bid landed");

        // Hammer revokes the key; isOperatorActive flips false.
        vm.prank(address(hammer));
        session.revokeOperatorKey(opKeyId);
        assertFalse(session.isOperatorActive(opKeyId), "revoked key inactive");

        // A subsequent bid under the revoked key reverts UnknownOperator.
        uint128 amount2 = uint128(RESERVE_PRICE) + uint128(RESERVE_PRICE) / 10;
        Ceiling memory c = _ceiling(alice, 10 ether, keccak256("B22-salt"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);
        AttestationQuote memory q = _quote(c, amount2, 1, uint128(RESERVE_PRICE), _qnonce("B22b", 1), operatorPk);

        vm.prank(alice);
        vm.expectRevert(ISessionAuction.UnknownOperator.selector);
        session.placeBid(c, LOT_ID, alice, 1, amount2, sig, opKeyId, q);
    }

    // BadAttestationSig: P256.verify rejection (bad sig, high-S, degenerate, off-curve).

    /// @dev Random r/s that do not verify against the registered key -> BadAttestationSig. Records
    ///      logs across the revert and pins no partial state mutation (winnerSeq 0, highBidder 0,
    ///      alice's free == full deposit), so no emit/commit precedes the P256.verify guard.
    function test_RevertWhen_BadAttestationSig() public {
        _initSession(address(0));
        _openLot();
        _mockPaddle(alice, PADDLE_ALICE);
        uint256 funded = 10 ether;
        _depositNative(alice, funded);

        // Fresh lot: the no-partial-commit baseline is the empty top.
        assertEq(uint256(session.getLot(LOT_ID).winnerSeq), 0, "no bid yet (winnerSeq 0)");
        assertEq(session.getLot(LOT_ID).highBidder, address(0), "no top bidder yet");
        assertEq(session.withdrawableFree(LOT_ID, alice), funded, "full deposit free, nothing committed");

        uint128 amount = uint128(RESERVE_PRICE);
        Ceiling memory c = _ceiling(alice, 5 ether, keccak256("B07-salt"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);

        // Proper-shaped but non-verifying r/s (small, in-range, s <= HALF_N), registered key.
        AttestationQuote memory q = AttestationQuote({
            mrEnclave: MR_ENCLAVE,
            vendorRoot: VENDOR_ROOT,
            observedPrevTop: bytes32(uint256(0)),
            nonce: _qnonce("B07", 0),
            r: bytes32(uint256(1)),
            s: bytes32(uint256(2))
        });
        vm.recordLogs();
        vm.prank(alice);
        vm.expectRevert(ISessionAuction.BadAttestationSig.selector);
        session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
        _assertNoBidEvents(vm.getRecordedLogs());

        // No partial commit on the attestation reject path: no top, no escrow moved.
        Lot memory lot = session.getLot(LOT_ID);
        assertEq(uint256(lot.winnerSeq), 0, "winnerSeq did NOT advance on a bad-sig reject");
        assertEq(lot.highBidder, address(0), "no top recorded on a bad-sig reject");
        assertEq(lot.highBid, 0, "no top amount recorded on a bad-sig reject");
        assertEq(session.withdrawableFree(LOT_ID, alice), funded, "alice free == full deposit (no spurious commit)");
    }

    /// @dev A high-S signature (s > HALF_N) is rejected by P256.verify -> BadAttestationSig. Built
    ///      by signing correctly then un-normalizing s to the high half (s' = N - s).
    function test_RevertWhen_HighSAttestation() public {
        _initSession(address(0));
        _openLot();
        _mockPaddle(alice, PADDLE_ALICE);
        _depositNative(alice, 10 ether);

        uint128 amount = uint128(RESERVE_PRICE);
        Ceiling memory c = _ceiling(alice, 5 ether, keccak256("B07h-salt"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);

        AttestationQuote memory q = AttestationQuote({
            mrEnclave: MR_ENCLAVE,
            vendorRoot: VENDOR_ROOT,
            observedPrevTop: bytes32(uint256(0)),
            nonce: _qnonce("B07h", 0),
            r: bytes32(0),
            s: bytes32(0)
        });
        bytes32 digest = _actionDigest(c, LOT_ID, amount, 0, q);
        (bytes32 r, bytes32 s) = vm.signP256(operatorPk, digest);

        // Force the HIGH half: if already low, flip to high; the resulting s > HALF_N is rejected.
        uint256 su = uint256(s);

        if (su <= P256_HALF_N) {
            su = P256_N - su;
        }

        q.r = r;
        q.s = bytes32(su);
        assertGt(uint256(q.s), P256_HALF_N, "s is in the high half (malleable)");

        vm.prank(alice);
        vm.expectRevert(ISessionAuction.BadAttestationSig.selector);
        session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
    }

    /// @dev A degenerate signature (r == 0, then s == 0) is rejected -> BadAttestationSig.
    function test_RevertWhen_DegenerateAttestationSig() public {
        _initSession(address(0));
        _openLot();
        _mockPaddle(alice, PADDLE_ALICE);
        _depositNative(alice, 10 ether);

        uint128 amount = uint128(RESERVE_PRICE);
        Ceiling memory c = _ceiling(alice, 5 ether, keccak256("B07d-salt"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);

        // r == 0
        AttestationQuote memory qr0 = AttestationQuote({
            mrEnclave: MR_ENCLAVE,
            vendorRoot: VENDOR_ROOT,
            observedPrevTop: bytes32(uint256(0)),
            nonce: _qnonce("B07d", 0),
            r: bytes32(uint256(0)),
            s: bytes32(uint256(1))
        });

        vm.prank(alice);
        vm.expectRevert(ISessionAuction.BadAttestationSig.selector);
        session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, qr0);

        // s == 0
        AttestationQuote memory qs0 = AttestationQuote({
            mrEnclave: MR_ENCLAVE,
            vendorRoot: VENDOR_ROOT,
            observedPrevTop: bytes32(uint256(0)),
            nonce: _qnonce("B07d", 1),
            r: bytes32(uint256(1)),
            s: bytes32(uint256(0))
        });

        vm.prank(alice);
        vm.expectRevert(ISessionAuction.BadAttestationSig.selector);
        session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, qs0);
    }

    /// @dev An off-curve registered key makes P256.verify fail its public-key validity check ->
    ///      BadAttestationSig, so verify fails closed even if such a key is somehow seeded. The
    ///      session is seeded with the off-curve fixture key.
    function test_RevertWhen_OffCurveOperatorKey() public {
        // Fresh clone seeded with the off-curve fixture key.
        _initSessionOffCurve(address(0));
        _openLot();
        _mockPaddle(alice, PADDLE_ALICE);
        _depositNative(alice, 10 ether);

        bytes32 offCurveKeyId =
            keccak256(abi.encode(keccak256("OPERATOR_QX_FIXTURE"), keccak256("OPERATOR_QY_FIXTURE")));
        assertTrue(session.isOperatorActive(offCurveKeyId), "off-curve key is registered/active");

        uint128 amount = uint128(RESERVE_PRICE);
        Ceiling memory c = _ceiling(alice, 5 ether, keccak256("B07oc-salt"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);
        // Proper-shaped r/s; verify fails on isValidPublicKey for the off-curve (qx, qy).
        AttestationQuote memory q = AttestationQuote({
            mrEnclave: MR_ENCLAVE,
            vendorRoot: VENDOR_ROOT,
            observedPrevTop: bytes32(uint256(0)),
            nonce: _qnonce("B07oc", 0),
            r: bytes32(uint256(1)),
            s: bytes32(uint256(2))
        });

        vm.prank(alice);
        vm.expectRevert(ISessionAuction.BadAttestationSig.selector);
        session.placeBid(c, LOT_ID, alice, 0, amount, sig, offCurveKeyId, q);
    }

    // Measurement is folded into the signed digest, not just the calldata equality check.

    /// @dev Calldata mrEnclave/vendorRoot equal the pinned expected measurement, but the P-256
    ///      signature is over a different measurement, so the recomputed digest mismatches and
    ///      P256.verify fails -> BadAttestationSig (not WrongMeasurement: the measurement-equality
    ///      check is never reached). This proves the predicate is more than "a registered key
    ///      signed this action". Records logs and pins the empty post-state.
    function test_RevertWhen_MeasurementSignedDiffersFromCalldata() public {
        _initSession(address(0));
        _openLot();
        _mockPaddle(alice, PADDLE_ALICE);
        uint256 funded = 10 ether;
        _depositNative(alice, funded);

        assertEq(uint256(session.getLot(LOT_ID).winnerSeq), 0, "no bid yet (winnerSeq 0)");
        assertEq(session.getLot(LOT_ID).highBidder, address(0), "no top bidder yet");
        assertEq(session.withdrawableFree(LOT_ID, alice), funded, "full deposit free, nothing committed");

        uint128 amount = uint128(RESERVE_PRICE);
        Ceiling memory c = _ceiling(alice, 5 ether, keccak256("B08-salt"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);

        // The calldata quote carries the correct pinned measurement (equality check would pass)...
        AttestationQuote memory q = AttestationQuote({
            mrEnclave: MR_ENCLAVE,
            vendorRoot: VENDOR_ROOT,
            observedPrevTop: bytes32(uint256(0)),
            nonce: _qnonce("B08", 0),
            r: bytes32(0),
            s: bytes32(0)
        });
        // ...but sign the digest over a forged mrEnclave so the recomputed digest (built from the
        // calldata measurement) does not match the signed bytes. Build signedOver as an independent
        // struct: a memory struct assignment aliases rather than copies, so mutating a copy of `q`
        // would corrupt `q.mrEnclave` too.
        AttestationQuote memory signedOver = AttestationQuote({
            mrEnclave: keccak256("FORGED_MRENCLAVE"),
            vendorRoot: q.vendorRoot,
            observedPrevTop: q.observedPrevTop,
            nonce: q.nonce,
            r: q.r,
            s: q.s
        });
        bytes32 digest = _actionDigest(c, LOT_ID, amount, 0, signedOver);
        (q.r, q.s) = _signP256LowS(operatorPk, digest);

        // BadAttestationSig (NOT WrongMeasurement): verify fails before the equality check.
        vm.recordLogs();
        vm.prank(alice);
        vm.expectRevert(ISessionAuction.BadAttestationSig.selector);
        session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
        _assertNoBidEvents(vm.getRecordedLogs());

        // No partial commit on this forged-measurement reject path.
        Lot memory lot = session.getLot(LOT_ID);
        assertEq(uint256(lot.winnerSeq), 0, "winnerSeq did NOT advance on a forged-measurement bad-sig reject");
        assertEq(lot.highBidder, address(0), "no top recorded on a forged-measurement bad-sig reject");
        assertEq(lot.highBid, 0, "no top amount recorded on a forged-measurement bad-sig reject");
        assertEq(session.withdrawableFree(LOT_ID, alice), funded, "alice free == full deposit (no spurious commit)");
    }

    // WrongMeasurement: a P256-valid sig over a wrong measurement passes verify, then the
    // measurement-equality check fires. Here calldata == signed, both wrong (unlike
    // test_RevertWhen_MeasurementSignedDiffersFromCalldata, which signs over a measurement that
    // differs from the calldata).

    /// @dev Calldata measurement != the pinned expected measurement, with the signature over that
    ///      same wrong measurement, so P256.verify passes and the equality check reverts
    ///      WrongMeasurement. Records logs and pins the empty post-state.
    function test_RevertWhen_WrongMeasurement() public {
        _initSession(address(0));
        _openLot();
        _mockPaddle(alice, PADDLE_ALICE);
        uint256 funded = 10 ether;
        _depositNative(alice, funded);

        assertEq(uint256(session.getLot(LOT_ID).winnerSeq), 0, "no bid yet (winnerSeq 0)");
        assertEq(session.withdrawableFree(LOT_ID, alice), funded, "full deposit free, nothing committed");

        uint128 amount = uint128(RESERVE_PRICE);
        Ceiling memory c = _ceiling(alice, 5 ether, keccak256("B09-salt"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);

        // Sign over the same wrong measurement the calldata carries: verify passes, equality fails.
        AttestationQuote memory q = AttestationQuote({
            mrEnclave: keccak256("WRONG_MRENCLAVE"),
            vendorRoot: VENDOR_ROOT,
            observedPrevTop: bytes32(uint256(0)),
            nonce: _qnonce("B09", 0),
            r: bytes32(0),
            s: bytes32(0)
        });
        bytes32 digest = _actionDigest(c, LOT_ID, amount, 0, q);
        (q.r, q.s) = _signP256LowS(operatorPk, digest);

        vm.recordLogs();
        vm.prank(alice);
        vm.expectRevert(ISessionAuction.WrongMeasurement.selector);
        session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
        _assertNoBidEvents(vm.getRecordedLogs());

        // No partial commit on the measurement reject path: no top, no escrow moved.
        Lot memory lot = session.getLot(LOT_ID);
        assertEq(uint256(lot.winnerSeq), 0, "winnerSeq did NOT advance on a wrong-measurement reject");
        assertEq(lot.highBidder, address(0), "no top recorded on a wrong-measurement reject");
        assertEq(lot.highBid, 0, "no top amount recorded on a wrong-measurement reject");
        assertEq(session.withdrawableFree(LOT_ID, alice), funded, "alice free == full deposit (no spurious commit)");
    }

    // QuoteNonceUsed: per-quote anti-replay on the attestation path.

    /// @dev Reuse of quote.nonce for the same operatorKeyId reverts QuoteNonceUsed. The reused-nonce
    ///      bid uses a valid ladder index (1) and a strictly-higher amount, isolating the quote-nonce
    ///      check from the keyed-nonce ladder. Asserts no bid events, free unchanged, highBid/winnerSeq
    ///      unchanged (the reused-nonce bid did not land), and that bidIndex 1 was not burned (a fresh
    ///      index-1 bid with a new quote nonce still lands).
    function test_RevertWhen_QuoteNonceReused() public {
        _initSession(address(0));
        _openLot();
        _depositNative(alice, 20 ether);

        bytes32 reusedNonce = _qnonce("B10", 0);

        // First bid (bidIndex 0) consumes the quote nonce under opKeyId; alice becomes the top.
        _placeValidBid(
            alice, alicePk, PADDLE_ALICE, 10 ether, keccak256("B10-salt"), 0, 0,
            uint128(RESERVE_PRICE), 0, reusedNonce, operatorPk, opKeyId, alice
        );
        assertEq(session.getLot(LOT_ID).highBidder, alice, "first bid landed (alice top)");

        // Snapshot the safe-direction signals before the reverting second bid: alice's free (read
        // from withdrawableFree, which a spurious second commit would decrement) and the standing top.
        uint256 aliceFreeBefore = session.withdrawableFree(LOT_ID, alice);
        Lot memory beforeLot = session.getLot(LOT_ID);
        assertEq(beforeLot.highBid, uint128(RESERVE_PRICE), "top is the first bid amount");
        assertEq(uint256(beforeLot.winnerSeq), 1, "first bid is seq 1");

        // Second bid (bidIndex 1, valid ladder, strictly-higher amount) reuses the same quote nonce
        // -> QuoteNonceUsed. Record logs to catch a partial emit/commit before the check.
        uint128 amount2 = uint128(RESERVE_PRICE) + uint128(RESERVE_PRICE) / 10;
        Ceiling memory c = _ceiling(alice, 10 ether, keccak256("B10-salt"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);
        AttestationQuote memory q = _quote(c, amount2, 1, uint128(RESERVE_PRICE), reusedNonce, operatorPk);

        vm.recordLogs();
        vm.prank(alice);
        vm.expectRevert(ISessionAuction.QuoteNonceUsed.selector);
        session.placeBid(c, LOT_ID, alice, 1, amount2, sig, opKeyId, q);
        _assertNoBidEvents(vm.getRecordedLogs());

        // The reused-nonce bid was fund-neutral and did NOT advance the top.
        assertEq(
            session.withdrawableFree(LOT_ID, alice),
            aliceFreeBefore,
            "reused-nonce bid moved no free escrow (no spurious commit of alice's free)"
        );
        Lot memory afterLot = session.getLot(LOT_ID);
        assertEq(afterLot.highBid, uint128(RESERVE_PRICE), "reused-nonce bid did NOT land (top unchanged)");
        assertEq(uint256(afterLot.winnerSeq), 1, "winnerSeq unchanged (reused-nonce bid did not advance the top)");
        assertEq(afterLot.highBidder, alice, "top bidder unchanged");

        // The keyed nonce rolled back: a fresh valid bid at index 1 with a new quote nonce must
        // succeed (if the reverted call had consumed index 1 this would revert InvalidAccountNonce).
        AttestationQuote memory qFresh = _quote(c, amount2, 1, uint128(RESERVE_PRICE), _qnonce("B10b", 1), operatorPk);

        vm.prank(alice);
        session.placeBid(c, LOT_ID, alice, 1, amount2, sig, opKeyId, qFresh);

        Lot memory landed = session.getLot(LOT_ID);
        assertEq(landed.highBid, amount2, "fresh index-1 bid landed, proving index 1 was not burned by the revert");
        assertEq(uint256(landed.winnerSeq), 2, "the key advanced exactly once after the first bid (index 1 fresh)");
    }

    // Quote nonce is keyed by (operatorKeyId, nonce); two keys may reuse the same nonce.

    /// @dev Register a second real operator key; land a bid under key 1 with quote.nonce v, then a
    ///      bid under key 2 reusing v must not revert QuoteNonceUsed, proving the used-nonce set is
    ///      tracked per operator key (so one key being offline never blocks another).
    function test_QuoteNonceIndependentPerOperator() public {
        _initSession(address(0));

        // Register the second real key (onlyHammer).
        vm.prank(address(hammer));
        bytes32 returnedKeyId = session.registerOperatorKey(op2Qx, op2Qy);
        assertEq(returnedKeyId, op2KeyId, "registerOperatorKey returns keccak256(abi.encode(qx,qy))");
        assertTrue(session.isOperatorActive(op2KeyId), "second operator key active");

        _openLot();
        _depositNative(alice, 20 ether);

        bytes32 sharedNonce = _qnonce("B11", 0);

        // Bid 1 under K1 (operatorPk/opKeyId) with the shared nonce.
        _placeValidBid(
            alice, alicePk, PADDLE_ALICE, 10 ether, keccak256("B11-salt"), 0, 0,
            uint128(RESERVE_PRICE), 0, sharedNonce, operatorPk, opKeyId, alice
        );

        // Bid 2 under K2 (operator2Pk/op2KeyId) reusing the SAME quote nonce; must NOT revert
        // QuoteNonceUsed. The bid is otherwise valid (next ladder index, strictly higher amount).
        uint128 amount2 = uint128(RESERVE_PRICE) + uint128(RESERVE_PRICE) / 10;
        Ceiling memory c = _ceiling(alice, 10 ether, keccak256("B11-salt"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);
        AttestationQuote memory q = _quote(c, amount2, 1, uint128(RESERVE_PRICE), sharedNonce, operator2Pk);

        vm.prank(alice);
        session.placeBid(c, LOT_ID, alice, 1, amount2, sig, op2KeyId, q);

        // The second bid landed under K2 (top advanced), proving the nonce spaces are independent.
        assertEq(session.getLot(LOT_ID).highBid, amount2, "K2 bid landed despite reusing K1's nonce");
    }

    // StalePrevTop: the quote's observedPrevTop must match the live top.

    /// @dev With lot.highBid == T (one prior bid landed), a valid envelope + key + P256 quote whose
    ///      observedPrevTop = X != T reverts StalePrevTop before the min-increment floor check and
    ///      the escrow commit: no winnerSeq increment, no escrow movement for either bidder, no
    ///      events. This blocks a host that lies observedPrevTop = ceiling - minIncrement to coerce
    ///      the policy into a ceiling-valued bid that would leak the bidder's maxBid.
    function test_RevertWhen_StalePrevTop() public {
        _initSession(address(0));
        _openLot();

        // Prior top: bidder1 (bob) lands T == RESERVE_PRICE so lot.highBid == T.
        _depositNative(bob, 20 ether);
        _placeValidBid(
            bob, bobPk, PADDLE_BOB, 10 ether, keccak256("B12-bob"), 0, 0,
            uint128(RESERVE_PRICE), 0, _qnonce("B12bob", 0), operatorPk, opKeyId, bob
        );
        uint128 T = uint128(RESERVE_PRICE);
        assertEq(session.getLot(LOT_ID).highBid, T, "prior top T landed");

        // Snapshot fund state so the revert can be shown fund-neutral. alice's free is read from
        // withdrawableFree (observable regardless of top status); the _deposit().committed value is
        // trivially 0 here (alice is never top), so it cannot detect a spurious commit of her funds.
        _depositNative(alice, 20 ether);
        uint256 aliceFreeBefore = session.withdrawableFree(LOT_ID, alice);
        Deposit memory bBefore = _depositOf(bob);
        uint64 seqBefore = session.getLot(LOT_ID).winnerSeq;

        // The host lies observedPrevTop = ceiling - minIncrement (X != T) to coerce a ceiling-valued
        // bid. The lie does not match live chain state, so the bid reverts StalePrevTop: a missed
        // bid, never a leak.
        uint128 ceiling = 10 ether;
        uint128 minInc = uint128((uint256(T) * MIN_INCREMENT_BPS) / 10_000);
        uint128 liedPrevTop = ceiling - minInc; // the lied near-ceiling value
        uint128 amount = ceiling; // what the honest policy would broadcast against the lied top

        Ceiling memory c = _ceiling(alice, ceiling, keccak256("B12-alice"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);
        AttestationQuote memory q = _quote(c, amount, 0, liedPrevTop, _qnonce("B12a", 0), operatorPk);

        // Record logs across the revert: no bid event may fire before the StalePrevTop check.
        vm.recordLogs();
        vm.prank(alice);
        vm.expectRevert(ISessionAuction.StalePrevTop.selector);
        session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
        _assertNoBidEvents(vm.getRecordedLogs());

        // Safe-direction post-state: nothing moved. The lied ceiling-valued bid did NOT land.
        Lot memory lot = session.getLot(LOT_ID);
        assertEq(lot.highBid, T, "top unchanged (no ceiling-valued bid landed)");
        assertEq(lot.highBidder, bob, "prior top bidder unchanged");
        assertEq(lot.winnerSeq, seqBefore, "_bidSeq did not increment");

        // alice's withdrawable free is unchanged, so nothing moved her funds: the commit that the
        // committed-bucket value (0 for a non-top bidder) cannot detect.
        assertEq(session.withdrawableFree(LOT_ID, alice), aliceFreeBefore, "alice free unchanged (no spurious commit)");

        Deposit memory bAfter = _depositOf(bob);
        assertEq(bAfter.free, bBefore.free, "bob free unchanged (no refund)");
        assertEq(bAfter.committed, bBefore.committed, "bob committed unchanged (still top)");
    }

    /// @dev StalePrevTop must also fire when the live top is ZERO. The attack on a fresh lot is a
    ///      host lying observedPrevTop = ceiling - minIncrement to coerce the policy
    ///      min(prevTop + minIncrement, ceiling) into a ceiling-valued first bid; the lie is a
    ///      nonzero phantom top against a zero live top. The check is observedPrevTop != lot.highBid,
    ///      i.e. (ceiling - minIncrement) != 0, so it must revert (a guard that skipped the empty-lot
    ///      case would let the phantom-top bid land at amount == ceiling, leaking maxBid). A positive
    ///      control then pins the check as 0 == 0 (honest first bid passes), not skipped.
    function test_RevertWhen_StalePrevTopOnEmptyLot() public {
        _initSession(address(0));
        _openLot();

        // Fresh lot: the live top is the ZERO boundary (the 0 != X side of the check).
        Lot memory fresh = session.getLot(LOT_ID);
        assertEq(fresh.highBid, 0, "empty lot: live top is 0 (the 0-side boundary)");
        assertEq(fresh.highBidder, address(0), "empty lot: no top bidder yet");
        assertEq(uint256(fresh.winnerSeq), 0, "empty lot: winnerSeq 0");

        _mockPaddle(alice, PADDLE_ALICE);
        uint256 funded = 20 ether;
        _depositNative(alice, funded);
        uint256 aliceFreeBefore = session.withdrawableFree(LOT_ID, alice);
        assertEq(aliceFreeBefore, funded, "alice funded free == full deposit before the lied first bid");

        // The host lies a phantom near-ceiling prevTop on the empty lot. The honest policy computes
        // min(liedPrevTop + minIncrement, ceiling) = ceiling, so the broadcast amount is the ceiling
        // itself (the maxBid disclosure StalePrevTop exists to close). The lie is nonzero against a
        // zero live highBid, so the check (observedPrevTop != lot.highBid) is 0 != X and must revert.
        uint128 ceiling = 10 ether;
        uint128 minInc = uint128((uint256(ceiling) * MIN_INCREMENT_BPS) / 10_000);
        uint128 liedPrevTop = ceiling - minInc; // the lied near-ceiling phantom top
        uint128 amount = ceiling; // what the honest policy would broadcast against the phantom top
        assertTrue(liedPrevTop != 0, "the phantom top is nonzero (so 0 != X is the boundary under test)");
        assertTrue(uint256(liedPrevTop) != uint256(fresh.highBid), "phantom prevTop != live highBid (0)");

        Ceiling memory c = _ceiling(alice, ceiling, keccak256("B12empty-alice"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);
        AttestationQuote memory q = _quote(c, amount, 0, liedPrevTop, _qnonce("B12empty", 0), operatorPk);

        // No bid event may fire before the StalePrevTop check.
        vm.recordLogs();
        vm.prank(alice);
        vm.expectRevert(ISessionAuction.StalePrevTop.selector);
        session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
        _assertNoBidEvents(vm.getRecordedLogs());

        // Post-state: the phantom-top ceiling-valued bid did not land. The lot is still empty, alice's
        // deposit is still free, and the revert rolled back the nonce (bidIndex 0 stays available).
        Lot memory afterRevert = session.getLot(LOT_ID);
        assertEq(afterRevert.highBid, 0, "no ceiling-valued first bid landed (top still 0)");
        assertEq(afterRevert.highBidder, address(0), "no top bidder recorded on the phantom-top reject");
        assertEq(uint256(afterRevert.winnerSeq), 0, "winnerSeq did NOT advance on the phantom-top reject");
        assertEq(
            session.withdrawableFree(LOT_ID, alice),
            funded,
            "alice free == full deposit (no spurious commit of the would-be ceiling bid)"
        );

        // Positive control: the same first bid built honestly (observedPrevTop = 0 == live highBid) at
        // amount == RESERVE_PRICE (the empty-lot floor) must land. Pins the empty-lot check as 0 == 0
        // (honest first bid passes), not a skipped guard that would also let the phantom-top lie
        // through. bidIndex 0 is still available; the fresh quote nonce avoids QuoteNonceUsed.
        uint128 firstAmount = uint128(RESERVE_PRICE);
        AttestationQuote memory qOk = _quote(c, firstAmount, 0, 0, _qnonce("B12emptyOk", 0), operatorPk);

        vm.prank(alice);
        session.placeBid(c, LOT_ID, alice, 0, firstAmount, sig, opKeyId, qOk);

        Lot memory landed = session.getLot(LOT_ID);
        assertEq(landed.highBidder, alice, "honest first bid (observedPrevTop == 0 == live highBid) lands");
        assertEq(landed.highBid, firstAmount, "honest first bid landed at the reserve floor, not the ceiling");
        assertEq(uint256(landed.winnerSeq), 1, "the honest first bid is seq 1");
        assertTrue(landed.highBid != ceiling, "the empty-lot check did not pass the ceiling-valued lie (0 == 0, not skipped)");
    }

    // The signed action digest is EXACTLY the ordered 10-tuple; a reordered preimage fails verify.

    /// @dev An attestation over a reordered or short 10-field preimage produces a different digest
    ///      than the contract recomputes, so P256.verify fails -> BadAttestationSig. Three legs show
    ///      all positions load-bearing: (a) swap adjacent positions 2/3 (lotId/amount), (b) drop the
    ///      trailing position-10 observedPrevTop (a 9-field omission), (c) perturb the middle
    ///      position-7 q.nonce. Leg (a) also records logs and pins the empty post-state (no emit or
    ///      commit before the P256.verify guard).
    function test_RevertWhen_ActionDigestFieldMissing() public {
        _initSession(address(0));
        _openLot();
        _mockPaddle(alice, PADDLE_ALICE);
        uint256 funded = 10 ether;
        _depositNative(alice, funded);

        assertEq(uint256(session.getLot(LOT_ID).winnerSeq), 0, "no bid yet (winnerSeq 0)");
        assertEq(session.getLot(LOT_ID).highBidder, address(0), "no top bidder yet");
        assertEq(session.withdrawableFree(LOT_ID, alice), funded, "full deposit free, nothing committed");

        uint128 amount = uint128(RESERVE_PRICE);
        Ceiling memory c = _ceiling(alice, 5 ether, keccak256("B13-salt"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);

        AttestationQuote memory q = AttestationQuote({
            mrEnclave: MR_ENCLAVE,
            vendorRoot: VENDOR_ROOT,
            observedPrevTop: bytes32(uint256(0)),
            nonce: _qnonce("B13", 0),
            r: bytes32(0),
            s: bytes32(0)
        });

        // (a) Sign over a reordered preimage: swap positions 2/3 (lotId and amount). The contract
        // hashes {SESSION_ID, lotId, amount, ...}; this signs {SESSION_ID, amount, lotId, ...}, a
        // distinct digest, so verify fails. This leg also records logs and pins the empty post-state.
        bytes32 reordered = keccak256(
            abi.encode(
                SESSION_ID,
                amount,   // swapped
                LOT_ID,   // swapped
                c.nonceKey,
                uint64(0),
                c.ceilingCommit,
                q.nonce,
                q.mrEnclave,
                q.vendorRoot,
                q.observedPrevTop
            )
        );
        (q.r, q.s) = _signP256LowS(operatorPk, reordered);

        vm.recordLogs();
        vm.prank(alice);
        vm.expectRevert(ISessionAuction.BadAttestationSig.selector);
        session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
        _assertNoBidEvents(vm.getRecordedLogs());

        // No partial commit on the reordered-digest reject path: no top, no escrow moved.
        Lot memory lot = session.getLot(LOT_ID);
        assertEq(uint256(lot.winnerSeq), 0, "winnerSeq did NOT advance on a reordered-digest reject");
        assertEq(lot.highBidder, address(0), "no top recorded on a reordered-digest reject");
        assertEq(lot.highBid, 0, "no top amount recorded on a reordered-digest reject");
        assertEq(session.withdrawableFree(LOT_ID, alice), funded, "alice free == full deposit (no spurious commit)");

        // (b) Trailing field dropped: sign over a nine-field preimage omitting position-10
        // q.observedPrevTop. The calldata quote is a full 10-field quote (observedPrevTop == 0 == live
        // highBid), but the contract recomputes the 10-field digest, so verify fails against this
        // 9-field signature -> BadAttestationSig. bidIndex is still 0 (leg (a) consumed no nonce).
        {
            AttestationQuote memory q9 = AttestationQuote({
                mrEnclave: MR_ENCLAVE,
                vendorRoot: VENDOR_ROOT,
                observedPrevTop: bytes32(uint256(0)),
                nonce: _qnonce("B13drop", 0),
                r: bytes32(0),
                s: bytes32(0)
            });
            bytes32 nineField = keccak256(
                abi.encode(
                    SESSION_ID,
                    LOT_ID,
                    amount,
                    c.nonceKey,
                    uint64(0),
                    c.ceilingCommit,
                    q9.nonce,
                    q9.mrEnclave,
                    q9.vendorRoot
                    // q9.observedPrevTop OMITTED (the trailing field)
                )
            );
            (q9.r, q9.s) = _signP256LowS(operatorPk, nineField);

            vm.prank(alice);
            vm.expectRevert(ISessionAuction.BadAttestationSig.selector);
            session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q9);
        }

        // (c) Middle field perturbed (position 7): sign over a preimage whose q.nonce differs from the
        // calldata quote.nonce, all else identical. The contract recomputes the digest from the
        // calldata nonce, so verify fails -> BadAttestationSig, pinning position 7 as load-bearing.
        {
            AttestationQuote memory qn = AttestationQuote({
                mrEnclave: MR_ENCLAVE,
                vendorRoot: VENDOR_ROOT,
                observedPrevTop: bytes32(uint256(0)),
                nonce: _qnonce("B13nonce-calldata", 0),
                r: bytes32(0),
                s: bytes32(0)
            });
            bytes32 wrongNonceDigest = keccak256(
                abi.encode(
                    SESSION_ID,
                    LOT_ID,
                    amount,
                    c.nonceKey,
                    uint64(0),
                    c.ceilingCommit,
                    _qnonce("B13nonce-signed", 0), // a DIFFERENT nonce than calldata qn.nonce
                    qn.mrEnclave,
                    qn.vendorRoot,
                    qn.observedPrevTop
                )
            );
            (qn.r, qn.s) = _signP256LowS(operatorPk, wrongNonceDigest);

            vm.prank(alice);
            vm.expectRevert(ISessionAuction.BadAttestationSig.selector);
            session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, qn);
        }
    }

    // Phase / timing / min-increment guards (NotOpen / AuctionEnded / BidTooLow).

    /// @dev A non-Open lot (here never opened, so phase None) reverts NotOpen.
    function test_RevertWhen_PlaceBidNotOpen() public {
        _initSession(address(0));
        // Deliberately do NOT open LOT_ID (phase None != Open).
        _mockPaddle(alice, PADDLE_ALICE);

        uint128 amount = uint128(RESERVE_PRICE);
        Ceiling memory c = _ceiling(alice, 5 ether, keccak256("B14n-salt"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);
        AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B14n", 0), operatorPk);

        vm.prank(alice);
        vm.expectRevert(ISessionAuction.NotOpen.selector);
        session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
    }

    /// @dev The endsAt guard is STRICT (block.timestamp < endsAt). A bid at exactly endsAt reverts
    ///      AuctionEnded; a bid at endsAt+1 reverts AuctionEnded; a bid at endsAt-1 passes the timing
    ///      gate (lands). Pins the boundary the soft-close window subtraction depends on.
    function test_RevertWhen_AuctionEnded() public {
        _initSession(address(0));
        uint64 endsAt = uint64(block.timestamp + 1 days);
        _openLot(endsAt);
        _depositNative(alice, 20 ether);

        uint128 amount = uint128(RESERVE_PRICE);

        // (i) exactly endsAt -> AuctionEnded (strict <).
        vm.warp(endsAt);
        {
            _mockPaddle(alice, PADDLE_ALICE);
            Ceiling memory c = _ceiling(alice, 10 ether, keccak256("B14e-salt"), 0);
            bytes memory sig = _signCeiling(address(session), alicePk, c);
            AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B14e", 0), operatorPk);

            vm.prank(alice);
            vm.expectRevert(ISessionAuction.AuctionEnded.selector);
            session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
        }

        // (ii) endsAt + 1 -> AuctionEnded.
        vm.warp(uint256(endsAt) + 1);
        {
            Ceiling memory c = _ceiling(alice, 10 ether, keccak256("B14e-salt"), 0);
            bytes memory sig = _signCeiling(address(session), alicePk, c);
            AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B14e2", 0), operatorPk);

            vm.prank(alice);
            vm.expectRevert(ISessionAuction.AuctionEnded.selector);
            session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
        }

        // (iii) endsAt - 1 -> passes the timing gate and lands (boundary pin: bids ARE accepted
        //       strictly before endsAt). Fresh quote nonce; bidIndex still 0 (prior attempts
        //       reverted before consuming the nonce).
        vm.warp(uint256(endsAt) - 1);
        {
            Ceiling memory c = _ceiling(alice, 10 ether, keccak256("B14e-salt"), 0);
            bytes memory sig = _signCeiling(address(session), alicePk, c);
            AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B14e3", 0), operatorPk);

            vm.prank(alice);
            session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
            assertEq(session.getLot(LOT_ID).highBid, amount, "bid at endsAt-1 lands");
        }
    }

    /// @dev With no prior top, the minimum bid is the reserve price. amount == reserve - 1 reverts
    ///      BidTooLow and moves no escrow / no seq; amount == reserve succeeds (boundary).
    function test_RevertWhen_BidTooLow() public {
        _initSession(address(0));
        _openLot();
        _depositNative(alice, 20 ether);

        // (i) amount == RESERVE_PRICE - 1 (one below the min bid) -> BidTooLow.
        uint128 tooLow = uint128(RESERVE_PRICE) - 1;
        {
            _mockPaddle(alice, PADDLE_ALICE);
            Deposit memory aBefore = _deposit(alice);
            uint64 seqBefore = session.getLot(LOT_ID).winnerSeq;

            Ceiling memory c = _ceiling(alice, 10 ether, keccak256("B14l-salt"), 0);
            bytes memory sig = _signCeiling(address(session), alicePk, c);
            AttestationQuote memory q = _quote(c, tooLow, 0, 0, _qnonce("B14l", 0), operatorPk);

            vm.prank(alice);
            vm.expectRevert(ISessionAuction.BidTooLow.selector);
            session.placeBid(c, LOT_ID, alice, 0, tooLow, sig, opKeyId, q);

            Deposit memory aAfter = _deposit(alice);
            assertEq(aAfter.committed, aBefore.committed, "no escrow committed on BidTooLow");
            assertEq(aAfter.free, aBefore.free, "free unchanged on BidTooLow");
            assertEq(session.getLot(LOT_ID).winnerSeq, seqBefore, "no seq increment on BidTooLow");
        }

        // (ii) amount == RESERVE_PRICE (exactly the min bid) -> succeeds (boundary).
        {
            uint128 atFloor = uint128(RESERVE_PRICE);
            Ceiling memory c = _ceiling(alice, 10 ether, keccak256("B14l-salt"), 0);
            bytes memory sig = _signCeiling(address(session), alicePk, c);
            AttestationQuote memory q = _quote(c, atFloor, 0, 0, _qnonce("B14l2", 0), operatorPk);

            vm.prank(alice);
            session.placeBid(c, LOT_ID, alice, 0, atFloor, sig, opKeyId, q);
            assertEq(session.getLot(LOT_ID).highBid, atFloor, "bid at the reserve floor lands");
        }
    }

    /// @dev With a prior top T, the minimum bid is T + mulDiv(T, minIncrementBps, 10_000) (the
    ///      floor-rounded increment). A second-principal bid of T + inc - 1 (observedPrevTop == T,
    ///      so StalePrevTop passes) reverts BidTooLow with the prior top intact and the challenger's
    ///      escrow untouched; a bid of exactly T + inc lands. T == 1 ether and MIN_INCREMENT_BPS ==
    ///      200 give inc == 0.02 ether, an exactly representable boundary.
    function test_RevertWhen_BidTooLowAboveTop() public {
        _initSession(address(0));
        _openLot();

        // First top: alice lands T == RESERVE_PRICE so lot.highBid == T.
        _depositNative(alice, 20 ether);
        _placeValidBid(
            alice, alicePk, PADDLE_ALICE, 10 ether, keccak256("B14at-alice"), 0, 0,
            uint128(RESERVE_PRICE), 0, _qnonce("B14at-alice", 0), operatorPk, opKeyId, alice
        );
        uint128 T = uint128(RESERVE_PRICE);
        assertEq(session.getLot(LOT_ID).highBid, T, "prior top T landed");

        // The over-top floor: T + mulDiv(T, bps, 10_000). inc == 0.02 ether here, so the floor is
        // exactly T + inc.
        uint128 inc = uint128((uint256(T) * MIN_INCREMENT_BPS) / 10_000);
        assertGt(inc, 0, "over-top increment is non-zero so the boundary is meaningful");

        // bob challenges. observedPrevTop == T (the genuine live top), so StalePrevTop is NOT the
        // failure under test; the failure is purely the min-increment floor.
        _mockPaddle(bob, PADDLE_BOB);
        _depositNative(bob, 20 ether);

        // (i) amount == T + inc - 1 (one below the min bid) -> BidTooLow. Prior top and bob's escrow intact.
        {
            uint128 justBelow = T + inc - 1;
            Deposit memory bBefore = _deposit(bob);
            uint64 seqBefore = session.getLot(LOT_ID).winnerSeq;

            Ceiling memory c = _ceiling(bob, 10 ether, keccak256("B14at-bob"), 0);
            bytes memory sig = _signCeiling(address(session), bobPk, c);
            AttestationQuote memory q = _quote(c, justBelow, 0, T, _qnonce("B14at-bob", 0), operatorPk);

            vm.prank(bob);
            vm.expectRevert(ISessionAuction.BidTooLow.selector);
            session.placeBid(c, LOT_ID, bob, 0, justBelow, sig, opKeyId, q);

            Lot memory lot = session.getLot(LOT_ID);
            assertEq(lot.highBidder, alice, "prior top bidder unchanged on over-top BidTooLow");
            assertEq(lot.highBid, T, "top amount unchanged on over-top BidTooLow");
            assertEq(lot.winnerSeq, seqBefore, "no seq increment on over-top BidTooLow");

            Deposit memory bAfter = _deposit(bob);
            assertEq(bAfter.free, bBefore.free, "challenger free unchanged on over-top BidTooLow");
            assertEq(bAfter.committed, bBefore.committed, "challenger committed unchanged (never top)");
        }

        // (ii) amount == T + inc (exactly the min bid) -> lands (inclusive boundary). bob becomes
        //      the new top; the prior-top refund-to-free rebalance is exercised in the escrow tests.
        {
            uint128 atFloor = T + inc;
            Ceiling memory c = _ceiling(bob, 10 ether, keccak256("B14at-bob"), 0);
            bytes memory sig = _signCeiling(address(session), bobPk, c);
            AttestationQuote memory q = _quote(c, atFloor, 0, T, _qnonce("B14at-bob2", 0), operatorPk);

            vm.prank(bob);
            session.placeBid(c, LOT_ID, bob, 0, atFloor, sig, opKeyId, q);

            Lot memory lot = session.getLot(LOT_ID);
            assertEq(lot.highBid, atFloor, "bid at exactly T + inc clears the over-top floor and lands");
            assertEq(lot.highBidder, bob, "challenger is the new top at the floor boundary");
        }
    }

    // KYC gate (paddleOf == 0 -> Unauthorized) + whenNotPaused (placeBid is the only gated fn).

    /// @dev A fully valid attested bid for a principal with paddleOf == 0 reverts Unauthorized (the
    ///      KYC gate). No paddle is mocked, so the registry returns 0.
    function test_RevertWhen_PaddleUnregistered() public {
        _initSession(address(0));
        _openLot();
        _depositNative(alice, 20 ether);
        // Intentionally NO _mockPaddle(alice, ...): paddleOf(alice) == 0 (the registry default).

        uint128 amount = uint128(RESERVE_PRICE);
        Ceiling memory c = _ceiling(alice, 10 ether, keccak256("B15-salt"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);
        AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B15", 0), operatorPk);

        // paddleOf(alice) == 0 -> Unauthorized.
        vm.prank(alice);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
    }

    /// @dev Under pause, placeBid reverts EnforcedPause: the whenNotPaused gate fires before any
    ///      field/signature work, since nonReentrant does not revert on first entry. A non-placeBid
    ///      pull-exit (withdrawDeposit) is not pause-gated.
    function test_RevertWhen_PlaceBidPaused() public {
        _initSession(address(0));
        _openLot();

        vm.prank(pauser);
        session.pause();
        assertTrue(session.paused(), "clone paused");

        // Zero-valued envelope/quote: whenNotPaused fires first -> EnforcedPause.
        Ceiling memory c;
        AttestationQuote memory q;
        vm.prank(alice);
        vm.expectRevert(Pausable.EnforcedPause.selector);
        session.placeBid(c, LOT_ID, alice, 0, uint128(RESERVE_PRICE), "", bytes32(0), q);

        // A non-placeBid exit (withdrawDeposit with zero free) is reachable while paused: it
        // reverts its OWN guard (NothingToWithdraw), never EnforcedPause, proving placeBid is the
        // only whenNotPaused function.
        vm.prank(alice);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        session.withdrawDeposit(LOT_ID, 0);
    }

    // placeBid happy path: all state writes and the emitted events.

    /// @dev A valid envelope + real attestation with amount >= the min bid, sufficient free, and
    ///      observedPrevTop == lot.highBid bumps the bid sequence, writes the hot slot (highBidder ==
    ///      principal; paddleId == paddleOf(principal)), sets winnerSeq, records the seq-keyed ceiling
    ///      commitment and bid record, and emits BidPlaced / TopBidChanged / BidEscrowCommitted. No
    ///      AuctionExtended (the bid is outside the soft-close buffer window).
    function test_PlaceBidHappyPath() public {
        _initSession(address(0));
        _openLot(); // endsAt far in the future, so this bid is OUTSIDE the buffer window
        _mockPaddle(alice, PADDLE_ALICE);

        uint128 amount = uint128(RESERVE_PRICE);
        uint128 maxBid = 5 ether;
        bytes32 salt = keccak256("B16-salt");
        bytes32 ceilingCommit = _commit(maxBid, salt);

        uint256 depositAmount = 10 ether; // free > amount, leaving slack
        _depositNative(alice, depositAmount);

        Deposit memory before = _deposit(alice);
        assertEq(before.free, depositAmount, "free funded");
        assertEq(before.committed, 0, "nothing committed yet");

        Ceiling memory c = _ceiling(alice, maxBid, salt, 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);
        AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B16", 0), operatorPk);

        // Snapshot the soft-close state before the bid. This bid is outside the buffer, so endsAt
        // must not slide and sealedExtensions must stay 0. The three positive expectEmit checks do
        // not preclude an extra AuctionExtended, so an impl that always slides endsAt would pass
        // without these explicit assertions.
        uint64 endsAtBefore = session.getLot(LOT_ID).endsAt;
        assertEq(uint256(session.getLot(LOT_ID).sealedExtensions), 0, "no extensions before the bid");

        // The three always-on events for a fresh top bid (previousTop == address(0), released 0).
        vm.expectEmit(true, true, false, true, address(session));
        emit ISessionAuction.BidPlaced(LOT_ID, alice, amount, 1);
        vm.expectEmit(true, true, false, true, address(session));
        emit ISessionAuction.TopBidChanged(LOT_ID, alice, amount);
        vm.expectEmit(true, true, false, true, address(session));
        emit ISessionAuction.BidEscrowCommitted(LOT_ID, alice, amount, address(0), 0);

        // Assert no AuctionExtended fires for this out-of-buffer bid. Capture the recorded set
        // immediately after placeBid, before the warp/hammer/reveal below emit their own logs.
        vm.recordLogs();
        vm.prank(bidder3); // relayer-agnostic: msg.sender is a third party
        session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
        _assertNoAuctionExtended(vm.getRecordedLogs());

        // Hot-slot state writes.
        Lot memory lot = session.getLot(LOT_ID);
        assertEq(uint256(lot.winnerSeq), 1, "winnerSeq == ++_bidSeq == 1");
        assertEq(lot.highBid, amount, "highBid set");
        assertEq(lot.highBidder, alice, "highBidder == principal, NOT the relayer");
        assertEq(uint256(lot.paddleId), uint256(PADDLE_ALICE), "paddleId == paddleOf(principal)");

        // Soft-close did NOT fire for the out-of-buffer bid: endsAt unchanged, no extension counted.
        assertEq(uint256(lot.endsAt), uint256(endsAtBefore), "endsAt unchanged (no soft-close for an out-of-buffer bid)");
        assertEq(uint256(lot.sealedExtensions), 0, "no soft-close extension for an out-of-buffer bid");

        // Escrow rebalance: amount moved free -> committed (no external transfer).
        Deposit memory afterBid = _deposit(alice);
        assertEq(afterBid.committed, amount, "amount committed");
        assertEq(afterBid.free, depositAmount - amount, "free reduced by amount, slack retained");

        // Seq-keyed writes: the ceiling commitment and bid record stored under (lotId, seq). The
        // interface has no direct getter, so prove both via a reveal round-trip: drive the lot to
        // Hammered (winnerSeq == 1), then reveal(LOT_ID, 1, maxBid, salt) as alice. reveal opens the
        // stored commitment and requires msg.sender == the recorded principal, so success proves the
        // commitment stored for seq 1 == ceilingCommit and the recorded principal == alice.
        vm.warp(uint256(session.getLot(LOT_ID).endsAt) + 1);
        session.hammer(LOT_ID);
        assertEq(uint256(session.getLot(LOT_ID).winnerSeq), 1, "winning seq is the recorded seq 1");

        vm.prank(alice); // the recorded principal of seq 1
        session.reveal(LOT_ID, 1, maxBid, salt);
        assertTrue(session.getLot(LOT_ID).revealed, "reveal on seq 1 opened the stored commitment + bid record");
    }

    /// @dev A bid INSIDE the soft-close buffer window slides endsAt and ALSO emits AuctionExtended
    ///      (the fourth event, emitted only when the bid extends the auction).
    function test_PlaceBidWithinBufferEmitsAuctionExtended() public {
        _initSession(address(0));
        // endsAt close enough that a bid lands inside the [endsAt - timeBuffer, endsAt) window.
        uint64 endsAt = uint64(block.timestamp + TIME_BUFFER_SEC / 2);
        _openLot(endsAt);
        _mockPaddle(alice, PADDLE_ALICE);
        _depositNative(alice, 10 ether);

        uint128 amount = uint128(RESERVE_PRICE);
        Ceiling memory c = _ceiling(alice, 5 ether, keccak256("B16b-salt"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);
        AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B16b", 0), operatorPk);

        // All four events in emission order (BidPlaced, TopBidChanged, BidEscrowCommitted, then
        // AuctionExtended). AuctionExtended carries endsAt == bid time + timeBuffer.
        vm.expectEmit(true, true, false, true, address(session));
        emit ISessionAuction.BidPlaced(LOT_ID, alice, amount, 1);
        vm.expectEmit(true, true, false, true, address(session));
        emit ISessionAuction.TopBidChanged(LOT_ID, alice, amount);
        vm.expectEmit(true, true, false, true, address(session));
        emit ISessionAuction.BidEscrowCommitted(LOT_ID, alice, amount, address(0), 0);
        vm.expectEmit(true, false, false, true, address(session));
        emit ISessionAuction.AuctionExtended(LOT_ID, uint64(block.timestamp + TIME_BUFFER_SEC));

        vm.prank(alice);
        session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);

        Lot memory lot = session.getLot(LOT_ID);
        assertEq(uint256(lot.endsAt), block.timestamp + TIME_BUFFER_SEC, "endsAt slid by soft-close");
        assertEq(uint256(lot.sealedExtensions), 1, "one soft-close extension counted");
    }

    /// @dev The soft-close window is [endsAt - timeBuffer, endsAt), so its lower edge is inclusive.
    ///      Pins the exact edge, which an off-by-one (`>` exclusive vs the correct `>=`) would miss.
    ///      Leg 1 (inclusive edge, block.timestamp == endsAt - timeBuffer): a valid bid must extend
    ///      (AuctionExtended with newEndsAt == block.timestamp + timeBuffer, lot.endsAt slides,
    ///      sealedExtensions == 1).
    ///      Leg 2 (one second before the window, on a fresh lot): a valid bid must not extend (no
    ///      AuctionExtended, lot.endsAt unchanged, sealedExtensions == 0), pinning the edge as a real
    ///      boundary.
    function test_PlaceBidSoftCloseTriggerBoundary() public {
        _initSession(address(0));
        _mockPaddle(alice, PADDLE_ALICE);
        _mockPaddle(bob, PADDLE_BOB);

        uint128 amount = uint128(RESERVE_PRICE);

        // Leg 1: open with endsAt = start + 2*timeBuffer so the window [endsAt - timeBuffer, endsAt)
        // opens at start + timeBuffer (a reachable warp target, not the open instant); warp to that edge.
        uint64 start = uint64(block.timestamp);
        uint64 endsAt = start + uint64(TIME_BUFFER_SEC) * 2;
        _openLot(endsAt);
        _depositNative(alice, 10 ether);

        uint64 windowOpen = endsAt - uint64(TIME_BUFFER_SEC); // == start + TIME_BUFFER_SEC
        vm.warp(uint256(windowOpen));
        assertEq(uint256(block.timestamp), uint256(endsAt) - TIME_BUFFER_SEC, "at the exact inclusive window-open edge");
        assertLt(uint256(block.timestamp), uint256(endsAt), "still strictly before endsAt (timing gate open)");

        Ceiling memory cA = _ceiling(alice, 5 ether, keccak256("B16edge-alice"), 0);
        bytes memory sigA = _signCeiling(address(session), alicePk, cA);
        AttestationQuote memory qA = _quote(cA, amount, 0, 0, _qnonce("B16edge-a", 0), operatorPk);

        // The bid at the inclusive edge must emit AuctionExtended with newEndsAt == block.timestamp +
        // timeBuffer (the reset form); the exact arg is what an exclusive-`>` impl fails.
        vm.expectEmit(true, false, false, true, address(session));
        emit ISessionAuction.AuctionExtended(LOT_ID, uint64(block.timestamp + TIME_BUFFER_SEC));
        vm.prank(alice);
        session.placeBid(cA, LOT_ID, alice, 0, amount, sigA, opKeyId, qA);

        Lot memory lotA = session.getLot(LOT_ID);
        assertEq(uint256(lotA.endsAt), block.timestamp + TIME_BUFFER_SEC, "edge bid slid endsAt (inclusive lower edge honored)");
        assertEq(uint256(lotA.sealedExtensions), 1, "edge bid counted exactly one extension (>= edge, not >)");

        // Leg 2: a FRESH lot, identical geometry, bid ONE SECOND before the window opens. It must NOT
        // extend. Bob bids so the keyed-nonce ladder is independent of alice's leg-1 bid.
        uint256 lot2 = 2;
        uint64 start2 = uint64(block.timestamp);
        uint64 endsAt2 = start2 + uint64(TIME_BUFFER_SEC) * 2;
        vm.prank(address(hammer));
        session.openLot(lot2, seller, RESERVE_PRICE, endsAt2);

        fundEth(bob, 20 ether);
        vm.prank(bob);
        session.depositCeiling{value: 10 ether}(lot2, 10 ether);

        uint64 beforeWindow = endsAt2 - uint64(TIME_BUFFER_SEC) - 1; // one second before the inclusive edge
        vm.warp(uint256(beforeWindow));
        assertEq(uint256(block.timestamp), uint256(endsAt2) - TIME_BUFFER_SEC - 1, "exactly one second before the window opens");

        Ceiling memory cB = Ceiling({
            principal: bob,
            sessionId: SESSION_ID,
            lotId: lot2,
            ceilingCommit: _commit(5 ether, keccak256("B16edge-bob")),
            strategy: 0,
            deadline: uint64(block.timestamp + 7 days),
            maxBids: uint64(MAX_EXTENSIONS) + 8,
            nonceKey: _nonceKey(lot2, bob)
        });
        bytes memory sigB = _signCeiling(address(session), bobPk, cB);

        AttestationQuote memory qB = AttestationQuote({
            mrEnclave: MR_ENCLAVE,
            vendorRoot: VENDOR_ROOT,
            observedPrevTop: bytes32(uint256(0)),
            nonce: _qnonce("B16edge-b", 0),
            r: bytes32(0),
            s: bytes32(0)
        });
        bytes32 dB = keccak256(
            abi.encode(
                SESSION_ID, lot2, amount, cB.nonceKey, uint64(0),
                cB.ceilingCommit, qB.nonce, qB.mrEnclave, qB.vendorRoot, qB.observedPrevTop
            )
        );
        (qB.r, qB.s) = _signP256LowS(operatorPk, dB);

        uint64 endsAtBefore = session.getLot(lot2).endsAt;
        assertEq(uint256(session.getLot(lot2).sealedExtensions), 0, "no extensions on lot2 before the pre-window bid");

        // Assert no AuctionExtended fired: the bid landed before the window, so the soft-close must
        // not slide endsAt. Catches an over-wide lower edge.
        vm.recordLogs();
        vm.prank(bob);
        session.placeBid(cB, lot2, bob, 0, amount, sigB, opKeyId, qB);
        _assertNoAuctionExtended(vm.getRecordedLogs());

        Lot memory lotB = session.getLot(lot2);
        assertEq(lotB.highBid, amount, "pre-window bid still lands (timing gate is open, just outside the buffer)");
        assertEq(uint256(lotB.endsAt), uint256(endsAtBefore), "endsAt unchanged for a bid one second before the window");
        assertEq(uint256(lotB.sealedExtensions), 0, "no soft-close extension for a pre-window bid (lower edge is exclusive below the buffer)");
    }

    // maxBid never appears in calldata for any strategy; the quote r/s is the enclave sig.

    /// @dev placeBid carries Ceiling.ceilingCommit and a public uint128 amount but no maxBid and no
    ///      separate enclaveSig param (the quote's r/s is the enclave signature). For each strategy
    ///      {0,1,2} an honest bid lands with amount == min(prevTop + minIncrement, ceiling) (the
    ///      reserve floor for the first bid), never the ceiling. The compile-time binding to
    ///      ISessionAuction.placeBid is itself the proof that no maxBid/enclaveSig field exists.
    function test_MaxBidNeverInCalldata() public {
        // Three strategies, each on its own lot, all landing the on-policy capped increment.
        _initSession(address(0));

        for (uint8 strategy = 0; strategy < 3; strategy++) {
            uint256 lotId = uint256(100 + strategy);
            vm.prank(address(hammer));
            session.openLot(lotId, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));

            _mockPaddle(alice, PADDLE_ALICE);
            vm.prank(alice);
            session.depositCeiling{value: 10 ether}(lotId, 10 ether);

            uint128 ceiling = 8 ether;
            uint128 amount = uint128(RESERVE_PRICE); // first bid: min(0 + inc, ceiling) == reserve floor
            assertTrue(amount < ceiling, "on-policy amount is strictly below the ceiling, not == ceiling");

            Ceiling memory c = Ceiling({
                principal: alice,
                sessionId: SESSION_ID,
                lotId: lotId,
                ceilingCommit: _commit(ceiling, keccak256(abi.encode("B17-salt", strategy))),
                strategy: strategy,
                deadline: uint64(block.timestamp + 7 days),
                maxBids: uint64(MAX_EXTENSIONS) + 8,
                nonceKey: _nonceKey(lotId, alice)
            });
            bytes memory sig = _signCeiling(address(session), alicePk, c);

            AttestationQuote memory q = AttestationQuote({
                mrEnclave: MR_ENCLAVE,
                vendorRoot: VENDOR_ROOT,
                observedPrevTop: bytes32(uint256(0)),
                nonce: _qnonce("B17", strategy),
                r: bytes32(0),
                s: bytes32(0)
            });
            bytes32 digest = keccak256(
                abi.encode(
                    SESSION_ID, lotId, amount, c.nonceKey, uint64(0),
                    c.ceilingCommit, q.nonce, q.mrEnclave, q.vendorRoot, q.observedPrevTop
                )
            );
            (q.r, q.s) = _signP256LowS(operatorPk, digest);

            vm.prank(alice);
            session.placeBid(c, lotId, alice, 0, amount, sig, opKeyId, q);

            Lot memory lot = session.getLot(lotId);
            assertEq(lot.highBid, amount, "landed the public capped amount, not maxBid");
            assertTrue(lot.highBid != ceiling, "amount is not the ceiling (no maxBid leak)");
        }
    }

    // Commitment hiding under a secret salt, fuzzed.

    /// @dev A commitment opens with the secret salt but not with a salt recomputed from public
    ///      fields, and two distinct user seeds over the same maxBid produce distinct commits (so
    ///      maxBid is not dictionary-recoverable from public data). The preimage is abi.encode (not
    ///      packed) over a uint128 maxBid, matching the contract's keccak256(abi.encode(maxBid, salt)).
    function testFuzz_CommitmentHidingUnderSalt(uint128 maxBid, bytes32 userSeed) public view {
        // Secret, high-entropy salt derived from a user-held seed (NOT public fields).
        bytes32 secretSalt = keccak256(abi.encode("Hammer/ceilingSalt/v1", userSeed));
        bytes32 commit = keccak256(abi.encode(maxBid, secretSalt));

        // (1) The secret salt opens the commitment.
        assertTrue(_checkOpening(commit, maxBid, secretSalt), "secret salt opens the commitment");

        // (2) A salt recomputed from PUBLIC fields (sessionId, lotId, principal) is != the secret
        //     salt and does NOT open the commitment (the hiding property).
        bytes32 publicDerivedSalt = keccak256(abi.encode(SESSION_ID, LOT_ID, address(this)));
        // With overwhelming probability the public salt differs from the secret one; guard the
        // degenerate equality so the assertion is meaningful.
        if (publicDerivedSalt != secretSalt) {
            assertFalse(_checkOpening(commit, maxBid, publicDerivedSalt), "public-derived salt does not open");
        }

        // (3) A DISTINCT user seed yields a distinct salt and hence a distinct commitment over the
        //     same maxBid (so a chain reader cannot equate commits to recover maxBid).
        bytes32 otherSeed = keccak256(abi.encode("OTHER", userSeed));
        bytes32 otherSalt = keccak256(abi.encode("Hammer/ceilingSalt/v1", otherSeed));
        bytes32 otherCommit = keccak256(abi.encode(maxBid, otherSalt));
        assertTrue(commit != otherCommit, "distinct seeds -> distinct commits over the same maxBid");
    }

    /// @dev Local mirror of the contract's commitment opening check: keccak256(abi.encode(maxBid, salt)).
    function _checkOpening(bytes32 commit, uint128 maxBid, bytes32 salt) private pure returns (bool) {
        return commit == keccak256(abi.encode(maxBid, salt));
    }

    // Snipe (strategy 1) re-arm: a stale snipe cannot leak maxBid or overpay.

    /// @dev Arm a snipe (strategy 1) bound to prevTop T0; a competing bid raises lot.highBid to
    ///      T1 > T0. (a) the stale snipe (observedPrevTop = T0) reverts StalePrevTop, a missed bid
    ///      with no overpay; (a2) the re-fed stale snipe (host re-feeds T1 into observedPrevTop so
    ///      StalePrevTop passes, but broadcasts the stale amount min(T0 + inc, ceiling), now below
    ///      the raised floor T1 + inc) reverts BidTooLow, the second way a stale snipe could fail;
    ///      (b) a re-signed snipe (observedPrevTop = T1, amount = min(T1 + inc, ceiling)) lands, with
    ///      amount != ceiling.
    function test_StaleSnipeRevertsThenReArms() public {
        _initSession(address(0));
        _openLot();

        // T0: bob lands the first top at the reserve floor.
        _depositNative(bob, 30 ether);
        _placeValidBid(
            bob, bobPk, PADDLE_BOB, 20 ether, keccak256("B19-bob0"), 0, 0,
            uint128(RESERVE_PRICE), 0, _qnonce("B19bob0", 0), operatorPk, opKeyId, bob
        );
        uint128 T0 = uint128(RESERVE_PRICE);

        // alice arms a snipe at prevTop = T0 (strategy 1) but does NOT broadcast yet.
        _mockPaddle(alice, PADDLE_ALICE);
        _depositNative(alice, 30 ether);
        uint128 ceiling = 25 ether;
        uint128 inc0 = uint128((uint256(T0) * MIN_INCREMENT_BPS) / 10_000);
        uint128 snipeAmt0 = T0 + inc0; // min(T0 + inc, ceiling), below ceiling
        Ceiling memory cAlice = _ceiling(alice, ceiling, keccak256("B19-alice"), 1); // strategy 1
        bytes memory sigAlice = _signCeiling(address(session), alicePk, cAlice);
        AttestationQuote memory staleQ = _quote(cAlice, snipeAmt0, 0, T0, _qnonce("B19a", 0), operatorPk);

        // A competing bid lands: bob raises the top to T1 > T0 (bidIndex 1, ladder for bob).
        uint128 T1 = T0 + uint128((uint256(T0) * MIN_INCREMENT_BPS) / 10_000) + 1; // strictly higher
        {
            Ceiling memory cBob = _ceiling(bob, 20 ether, keccak256("B19-bob0"), 0);
            bytes memory sigBob = _signCeiling(address(session), bobPk, cBob);
            AttestationQuote memory qBob = _quote(cBob, T1, 1, T0, _qnonce("B19bob1", 1), operatorPk);
            vm.prank(bob);
            session.placeBid(cBob, LOT_ID, bob, 1, T1, sigBob, opKeyId, qBob);
            assertEq(session.getLot(LOT_ID).highBid, T1, "competing bid raised the top to T1");
        }

        // (a) The stale snipe (observedPrevTop == T0 != live T1) reverts StalePrevTop: a missed bid,
        //     never an overpay. Read free from withdrawableFree (the committed bucket is a trivial 0
        //     since alice is never top), and record logs so a partial emit before the check is caught.
        uint256 aliceFreeBefore = session.withdrawableFree(LOT_ID, alice);
        vm.recordLogs();
        vm.prank(alice);
        vm.expectRevert(ISessionAuction.StalePrevTop.selector);
        session.placeBid(cAlice, LOT_ID, alice, 0, snipeAmt0, sigAlice, opKeyId, staleQ);
        _assertNoBidEvents(vm.getRecordedLogs());
        assertEq(
            session.withdrawableFree(LOT_ID, alice),
            aliceFreeBefore,
            "stale snipe moved no free escrow (no spurious commit)"
        );
        // bob is still the live top, so his committed (== live highBid) must be exactly T1: the
        // stale snipe leaked no prior-top refund and did not advance the top.
        assertEq(session.getLot(LOT_ID).highBidder, bob, "stale snipe did not dethrone the live top");
        assertEq(session.getLot(LOT_ID).highBid, T1, "stale snipe did not change the top amount");

        // (a2) The re-fed stale snipe: the host re-feeds T1 into observedPrevTop so the StalePrevTop
        //      check passes, but broadcasts the stale amount snipeAmt0 == min(T0 + inc, ceiling), now
        //      below the raised floor over T1. It clears StalePrevTop and reverts at the min-increment
        //      floor with BidTooLow (a miss, never an overpay). Reuses bidIndex 0 (leg (a) consumed no
        //      nonce) with a fresh quote nonce; the floor revert rolls back the nonce, so leg (b) can
        //      still land at bidIndex 0.
        // snipeAmt0 == T0 + inc0 and T1 == T0 + inc0 + 1, so snipeAmt0 < T1 <= _minBid(lot),
        // independent of the contract's exact _minBid rounding.
        assertTrue(snipeAmt0 < T1, "stale amount is below the new top (so below the raised floor: BidTooLow)");
        uint256 aliceFreeBeforeReFed = session.withdrawableFree(LOT_ID, alice);
        AttestationQuote memory reFedQ = _quote(cAlice, snipeAmt0, 0, T1, _qnonce("B19reFed", 0), operatorPk);
        vm.recordLogs();
        vm.prank(alice);
        vm.expectRevert(ISessionAuction.BidTooLow.selector);
        session.placeBid(cAlice, LOT_ID, alice, 0, snipeAmt0, sigAlice, opKeyId, reFedQ);
        _assertNoBidEvents(vm.getRecordedLogs());
        assertEq(
            session.withdrawableFree(LOT_ID, alice),
            aliceFreeBeforeReFed,
            "re-fed stale snipe moved no free escrow (missed bid, never an overpay)"
        );
        assertEq(session.getLot(LOT_ID).highBidder, bob, "re-fed stale snipe did not dethrone the live top");
        assertEq(session.getLot(LOT_ID).highBid, T1, "re-fed stale snipe did not change the top amount");

        // (b) Re-signed snipe against the live top T1, amount = min(T1 + inc, ceiling). bidIndex is
        //     still 0 (the stale attempts consumed no nonce). It lands and amount != ceiling: a snipe
        //     is a capped increment, never a reveal of the ceiling.
        uint128 inc1 = uint128((uint256(T1) * MIN_INCREMENT_BPS) / 10_000);
        uint128 snipeAmt1 = T1 + inc1;
        assertTrue(snipeAmt1 < ceiling, "re-armed snipe amount is below the ceiling, not == ceiling");
        AttestationQuote memory freshQ = _quote(cAlice, snipeAmt1, 0, T1, _qnonce("B19a2", 0), operatorPk);
        vm.prank(alice);
        session.placeBid(cAlice, LOT_ID, alice, 0, snipeAmt1, sigAlice, opKeyId, freshQ);

        Lot memory lot = session.getLot(LOT_ID);
        assertEq(lot.highBid, snipeAmt1, "re-armed snipe landed the capped increment");
        assertEq(lot.highBidder, alice, "alice is the new top");
        assertTrue(lot.highBid != ceiling, "snipe never reveals maxBid (amount != ceiling)");
    }

    // cancelEnvelope: self-sovereign, on-chain envelope revocation.

    /// @dev Principal P cancels nonceKey N (emits EnvelopeCancelled, sets the flag); a later placeBid
    ///      for P under N reverts EnvelopeRevoked. Revocation is enforced on-chain against the
    ///      enclave, not merely server-side.
    function test_CancelEnvelopeBlocksBid() public {
        _initSession(address(0));
        _openLot();
        _mockPaddle(alice, PADDLE_ALICE);
        _depositNative(alice, 10 ether);

        uint192 nk = _nonceKey(LOT_ID, alice);

        vm.expectEmit(true, true, false, false, address(session));
        emit ISessionAuction.EnvelopeCancelled(alice, nk);
        vm.prank(alice);
        session.cancelEnvelope(nk);
        assertTrue(session.envelopeCancelled(alice, nk), "cancellation flag set for (alice, nk)");

        // A later valid-looking bid under the cancelled nonceKey reverts EnvelopeRevoked.
        uint128 amount = uint128(RESERVE_PRICE);
        Ceiling memory c = _ceiling(alice, 5 ether, keccak256("B20-salt"), 0);
        bytes memory sig = _signCeiling(address(session), alicePk, c);
        AttestationQuote memory q = _quote(c, amount, 0, 0, _qnonce("B20", 0), operatorPk);

        vm.prank(alice);
        vm.expectRevert(ISessionAuction.EnvelopeRevoked.selector);
        session.placeBid(c, LOT_ID, alice, 0, amount, sig, opKeyId, q);
    }

    /// @dev cancelEnvelope keys strictly to msg.sender. Attacker A calling cancelEnvelope(N) where N
    ///      is victim B's nonceKey sets only envelopeCancelled[A][N]; B's flag stays false and B's bid
    ///      under N still authorizes (lands). An auth-isolation property.
    function test_CancelEnvelopeCannotTargetOther() public {
        _initSession(address(0));
        _openLot();

        // N is BOB's nonceKey. The attacker is alice.
        uint192 nB = _nonceKey(LOT_ID, bob);
        vm.prank(alice);
        session.cancelEnvelope(nB);

        assertTrue(session.envelopeCancelled(alice, nB), "attacker's own (A, N) flag is set");
        assertFalse(session.envelopeCancelled(bob, nB), "victim's (B, N) flag is NOT set");

        // Bob's bid under N still authorizes and lands (the attacker could not revoke it).
        _depositNative(bob, 10 ether);
        _placeValidBid(
            bob, bobPk, PADDLE_BOB, 5 ether, keccak256("B21-bob"), 0, 0,
            uint128(RESERVE_PRICE), 0, _qnonce("B21bob", 0), operatorPk, opKeyId, bob
        );
        assertEq(session.getLot(LOT_ID).highBidder, bob, "victim B's bid under N still authorizes");
    }

    // Operator roster management (onlyHammer; keyId; revoke effect). The placeBid-side revoke effect
    // is covered by test_RevokedKeyRejectedAtPlaceBid; here we pin the onlyHammer caller gate and the
    // register-then-active runtime effect.

    /// @dev (a) registerOperatorKey / revokeOperatorKey are onlyHammer (a non-hammer caller reverts
    ///      Unauthorized); (b) hammer register makes isOperatorActive(K) true and a bid under K
    ///      verifies. keyId == keccak256(abi.encode(qx, qy)) is asserted on register.
    function test_RevertWhen_RegisterKeyNotHammer() public {
        _initSession(address(0));

        // (a) non-hammer register -> Unauthorized.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        session.registerOperatorKey(op2Qx, op2Qy);

        // (a) non-hammer revoke -> Unauthorized.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        session.revokeOperatorKey(opKeyId);

        // (b) hammer registers K2: returned keyId is canonical and the key becomes active.
        vm.prank(address(hammer));
        bytes32 keyId = session.registerOperatorKey(op2Qx, op2Qy);
        assertEq(keyId, keccak256(abi.encode(op2Qx, op2Qy)), "keyId == keccak256(abi.encode(qx,qy))");
        assertTrue(session.isOperatorActive(op2KeyId), "registered key is active");

        // A bid under the newly-registered K2 verifies (lands), proving a still-registered 1-of-N
        // key authorizes.
        _openLot();
        _depositNative(alice, 10 ether);
        _placeValidBid(
            alice, alicePk, PADDLE_ALICE, 5 ether, keccak256("B22reg-salt"), 0, 0,
            uint128(RESERVE_PRICE), 0, _qnonce("B22reg", 0), operator2Pk, op2KeyId, alice
        );
        assertEq(session.getLot(LOT_ID).highBidder, alice, "bid under a freshly registered key lands");
    }

    // Active-bid bisection leaks at most one minIncrement by inference, never reads plaintext maxBid.

    /// @dev A capital-committing adversary walks lot.highBid up to ceiling - minIncrement using its
    ///      own genuine bids; the victim's next honest bid uses observedPrevTop == the genuine live
    ///      top, so StalePrevTop passes, and the resulting amount equals min(prevTop + inc, ceiling)
    ///      == ceiling. This at-ceiling bid is on-policy, not over-ceiling: challengeOverCeiling on it
    ///      reverts NotOverCeiling. No plaintext maxBid is ever read; the leak is bounded to one
    ///      minIncrement by inference from public bids.
    function test_ActiveBidBisectionIsBoundedInference() public {
        _initSession(address(0));
        _openLot();

        bytes32 victimSalt = keccak256("B23-victim-salt");

        // Adversary (bob) walks the top to a genuine probe just below the victim's ceiling. Define
        // the ceiling as probe + one minIncrement, so the min bid (== probe + mulDiv(probe, bps,
        // 10_000)) equals the ceiling and the on-policy capped amount lands at the ceiling boundary.
        uint128 probe = 5 ether;
        uint128 incP = uint128((uint256(probe) * MIN_INCREMENT_BPS) / 10_000); // contract's mulDiv floor
        uint128 ceiling = probe + incP; // the victim's committed ceiling (never on-chain)

        _depositNative(bob, 30 ether);
        _placeValidBid(
            bob, bobPk, PADDLE_BOB, 20 ether, keccak256("B23-bob"), 0, 0,
            probe, 0, _qnonce("B23bob", 0), operatorPk, opKeyId, bob
        );
        assertEq(session.getLot(LOT_ID).highBid, probe, "adversary walked the top to the probe value");

        // Victim's honest enclave responds against the GENUINE live top (observedPrevTop == probe),
        // so StalePrevTop passes. The on-policy amount is min(probe + inc, ceiling) == ceiling, and
        // it equals _minBid exactly, so it clears the floor at the boundary.
        uint128 victimAmount = ceiling;
        assertEq(victimAmount, probe + incP, "the bounded residual: victim's on-policy bid lands AT the ceiling");

        _mockPaddle(alice, PADDLE_ALICE);
        _depositNative(alice, 30 ether);
        Ceiling memory cV = _ceiling(alice, ceiling, victimSalt, 0);
        bytes memory sigV = _signCeiling(address(session), alicePk, cV);
        AttestationQuote memory qV = _quote(cV, victimAmount, 0, probe, _qnonce("B23v", 0), operatorPk);
        vm.prank(alice);
        session.placeBid(cV, LOT_ID, alice, 0, victimAmount, sigV, opKeyId, qV);

        Lot memory lot = session.getLot(LOT_ID);
        assertEq(lot.highBid, ceiling, "victim's bid landed AT the ceiling via genuine prevTop");
        assertEq(uint256(lot.winnerSeq), 2, "victim's bid is seq 2");

        // The at-ceiling bid is on-policy, not over-ceiling: challengeOverCeiling on seq 2 with the
        // true (ceiling, salt) opens the commitment, but the strict bidAmount > maxBid check is false,
        // so it reverts NotOverCeiling. Drive the lot to Hammered first so the seq is finalizable.
        vm.warp(uint256(session.getLot(LOT_ID).endsAt) + 1);
        session.hammer(LOT_ID);

        vm.prank(alice); // the recorded principal of seq 2
        vm.expectRevert(ISessionAuction.NotOverCeiling.selector);
        session.challengeOverCeiling(LOT_ID, 2, ceiling, victimSalt);
    }

    // No-tokenization surface + nonce ladder survives maxExtensions re-arms.

    /// @dev The bidding/privacy surface carries no tokenization symbol (ERC721Holder /
    ///      safeTransferFrom / lotToken / TitleAssigned). A static surface invariant: the
    ///      compile-time binding to ISessionAuction is the proof. Exercises a bid and confirms the
    ///      only privacy state written is the ceiling commitment (no token id, no title); the test
    ///      would fail to compile if a tokenization arg were ever added to placeBid.
    function test_NoTokenizationSurface() public {
        _initSession(address(0));
        _openLot();
        _mockPaddle(alice, PADDLE_ALICE);
        _depositNative(alice, 10 ether);

        // A normal bid: the only privacy object is the ceiling commitment carried in the envelope.
        bytes32 ceilingCommit = _commit(5 ether, keccak256("B24-salt"));
        Ceiling memory c = _ceiling(alice, 5 ether, keccak256("B24-salt"), 0);
        assertEq(c.ceilingCommit, ceilingCommit, "envelope carries a ceiling COMMITMENT, not a token");
        bytes memory sig = _signCeiling(address(session), alicePk, c);
        AttestationQuote memory q = _quote(c, uint128(RESERVE_PRICE), 0, 0, _qnonce("B24", 0), operatorPk);

        vm.prank(alice);
        session.placeBid(c, LOT_ID, alice, 0, uint128(RESERVE_PRICE), sig, opKeyId, q);

        // The packed Lot has no tokenId/title member (only highBid/highBidder/paddleId/escrowAmount/
        // commit roots); the struct binding is the static proof.
        Lot memory lot = session.getLot(LOT_ID);
        assertEq(lot.highBidder, alice, "bid recorded without any tokenization step");
    }

    /// @dev Drive several soft-close re-arms (bids inside the buffer window) and assert the
    ///      keyed-nonce ladder does NOT exhaust: bidIndex keeps incrementing across the re-arms up to
    ///      (but not exceeding) maxBids, with no InvalidAccountNonce. Pins the liveness margin: maxBids
    ///      exceeds the achievable extension count.
    function test_NonceLadderSurvivesSoftCloseReArms() public {
        _initSession(address(0));
        // Short window so each bid lands inside the soft-close buffer and re-arms endsAt.
        uint64 endsAt = uint64(block.timestamp + TIME_BUFFER_SEC / 2);
        _openLot(endsAt);
        _mockPaddle(alice, PADDLE_ALICE);
        _depositNative(alice, 500 ether);

        // Escalating bids, one per soft-close re-arm, each advancing the keyed-nonce ladder
        // (bidIndex 0,1,2,...). maxBids (== MAX_EXTENSIONS + 8) exceeds the count, so the ladder
        // never reverts InvalidAccountNonce.
        uint128 prevTop = 0;
        uint128 amount = uint128(RESERVE_PRICE);
        uint64 reArms = 6; // < maxBids and >= a few extensions
        for (uint64 i = 0; i < reArms; i++) {
            Ceiling memory c = _ceiling(alice, 400 ether, keccak256("B24n-salt"), 2); // proxy strategy
            bytes memory sig = _signCeiling(address(session), alicePk, c);
            AttestationQuote memory q = _quote(c, amount, i, prevTop, _qnonce("B24n", i), operatorPk);
            vm.prank(alice);
            session.placeBid(c, LOT_ID, alice, i, amount, sig, opKeyId, q);

            prevTop = amount;
            // next on-policy increment (kept well under the committed ceiling 400 ether).
            amount = amount + uint128((uint256(amount) * MIN_INCREMENT_BPS) / 10_000) + 1;
        }

        Lot memory lot = session.getLot(LOT_ID);
        assertEq(lot.highBid, prevTop, "the last re-armed bid is the standing top");
        assertEq(uint256(lot.winnerSeq), uint256(reArms), "the nonce ladder advanced once per re-arm");
        assertGe(uint256(lot.sealedExtensions), 1, "soft-close re-armed at least once without nonce exhaustion");
    }

    // Deposit accessors. The interface exposes withdrawableFree (free) but not committed directly;
    // committed is read from the packed Lot via getLot for the top bidder. A small struct mirror over
    // the two public views lets a test assert both buckets.

    /// @dev Read `who`'s deposit buckets. `free` comes from withdrawableFree; `committed` is the
    ///      lot's escrow attributed to them when they are the current top, else 0. The revert checks
    ///      only need that nothing changed, so this mirror is sufficient.
    function _deposit(address who) private view returns (Deposit memory d) {
        d.free = uint128(session.withdrawableFree(LOT_ID, who));
        Lot memory lot = session.getLot(LOT_ID);
        d.committed = (lot.highBidder == who) ? lot.highBid : 0;
    }

    /// @dev Same as _deposit but named for the previous-top bidder in two-party fund checks.
    function _depositOf(address who) private view returns (Deposit memory d) {
        return _deposit(who);
    }

    // Topic-0 (event signature) hashes for the bid-path events, used to prove a reverting placeBid
    // emitted none of them (no partial emit before a later guard fires).
    bytes32 private constant SIG_BID_PLACED =
        keccak256("BidPlaced(uint256,address,uint128,uint64)");
    bytes32 private constant SIG_TOP_BID_CHANGED =
        keccak256("TopBidChanged(uint256,address,uint128)");
    bytes32 private constant SIG_BID_ESCROW_COMMITTED =
        keccak256("BidEscrowCommitted(uint256,address,uint128,address,uint128)");
    bytes32 private constant SIG_AUCTION_EXTENDED =
        keccak256("AuctionExtended(uint256,uint64)");

    /// @dev Assert none of BidPlaced / TopBidChanged / BidEscrowCommitted appear in `logs`, catching
    ///      a partial-commit-then-revert that would otherwise pass behind the expected revert.
    function _assertNoBidEvents(Vm.Log[] memory logs) private pure {
        for (uint256 i = 0; i < logs.length; i++) {
            bytes32 topic0 = logs[i].topics.length == 0 ? bytes32(0) : logs[i].topics[0];
            assertTrue(topic0 != SIG_BID_PLACED, "no BidPlaced emitted before the revert");
            assertTrue(topic0 != SIG_TOP_BID_CHANGED, "no TopBidChanged emitted before the revert");
            assertTrue(topic0 != SIG_BID_ESCROW_COMMITTED, "no BidEscrowCommitted emitted before the revert");
        }
    }

    /// @dev Assert AuctionExtended is absent from `logs`: an out-of-buffer bid must not slide endsAt,
    ///      which a positive expectEmit on the other three bid events does not preclude.
    function _assertNoAuctionExtended(Vm.Log[] memory logs) private pure {
        for (uint256 i = 0; i < logs.length; i++) {
            bytes32 topic0 = logs[i].topics.length == 0 ? bytes32(0) : logs[i].topics[0];
            assertTrue(topic0 != SIG_AUCTION_EXTENDED, "no AuctionExtended for an out-of-buffer bid");
        }
    }
}
