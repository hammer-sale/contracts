// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// Settlement denomination parity: native ETH vs a 6-decimal ERC-20. Every settlement and delivery
// payout path behaves identically on both rails. Bid-derived amounts are equal modulo the 1e12 decimal
// scale (18-dp native vs 6-dp token); the dispute bond is a flat base-unit amount, identical on both
// rails (not scaled).
//
// Coverage:
//   - Full happy path (deposit -> bid -> hammer -> finalize -> deliver -> confirm) on each rail;
//     proceeds, fee, escrow, slack equal modulo 1e12.
//   - Payout matrix: confirmReceipt, releaseAfterWindow, reclaimUndelivered, and
//     openDispute + resolveDispute all pay on both rails; escrow + bond conserved; a repeated terminal
//     reverts WrongDeliveryState and moves no funds.
//   - Hostile-payee no-strand: a reverting native receiver or a false-returning ERC-20 is credited to
//     pending withdrawals (the push fails without reverting the terminal); the terminal still completes,
//     the disjoint party is paid, and claimPending later pulls the parked amount. Split per rail and per
//     payout path (confirm, gas-guzzler push cap, reclaim refund, dispute refund/release, bond recipient,
//     auto-release, fee recipient) so each fails independently.
//   - openDispute bond pull: each rail rejects the other rail's call shape with WrongBond and pulls
//     nothing; a missing allowance bubbles ERC20InsufficientAllowance; the bond debit is pinned to the
//     opener (a clone-balance delta alone cannot prove the bond came from the opener).
//   - Dust to seller: a non-divisible bid keeps the truncated-fee remainder with the seller, with no
//     wei lost on either rail.
//
// Conventions: negative assertions use a specific error selector; happy and conservation assertions use
// vm.expectEmit with checked args plus exact balance and state checks. Pre-state is built through the
// real entrypoints. Helpers are private to this contract.

import {HammerBase} from "./HammerBase.t.sol";

import {SessionAuction} from "../src/SessionAuction.sol";
import {Clones} from "@openzeppelin/contracts/proxy/Clones.sol";
import {ISessionAuction} from "../src/interfaces/ISessionAuction.sol";
import {IPaddleRegistry} from "../src/interfaces/IPaddleRegistry.sol";
import {MockERC20} from "./mocks/MockERC20.sol";

import {IERC1271} from "@openzeppelin/contracts/interfaces/IERC1271.sol";
import {IERC20Errors} from "@openzeppelin/contracts/interfaces/draft-IERC6093.sol";

import {
    Ceiling,
    AttestationQuote,
    InitConfig,
    Lot,
    LotPhase,
    DeliveryState,
    Resolution,
    CEILING_TYPEHASH
} from "../src/types/HammerTypes.sol";

/// @dev Native receiver that reverts on any value transfer while `reject` is true. Makes the gas-capped
///      push fail so the payout is credited to pending withdrawals instead of reverting the terminal.
///      Toggle `reject` off so a later `claimPending` can pull the parked amount.
contract H_RejectingReceiver {
    bool public reject = true;

    function setReject(bool v) external {
        reject = v;
    }

    receive() external payable {
        if (reject) revert("no ether");
    }
}

/// @dev ERC-20 whose `transfer` returns false (never reverts) while `fail` is true, so the clone's
///      try-transfer observes the false return and credits pending withdrawals instead of reverting.
///      `transferFrom` always succeeds so deposits and bond pulls work; only the push leg fails until
///      toggled.
contract H_FalseReturningERC20 is MockERC20 {
    bool public fail = true;

    constructor() MockERC20("False USD", "fUSD", 6) {}

    function setFail(bool v) external {
        fail = v;
    }

    function transfer(address to, uint256 value) public override returns (bool) {
        if (fail) return false; // false return parks the payout; it does not revert the terminal

        return super.transfer(to, value);
    }
}

/// @dev Native receiver that does not revert but burns past the 50_000-gas push cap inside `receive` via
///      cold SSTOREs, so the gas cap (not the revert branch) routes the payout to pending withdrawals.
///      An uncapped send would forward all gas and let this complete. Set `accept` so the uncapped
///      `claimPending` succeeds later.
contract H_GasGuzzlerReceiver {
    bool public accept;
    mapping(uint256 => uint256) private _sink; // distinct cold slots: each first write costs ~20k gas

    function setAccept(bool v) external {
        accept = v;
    }

    receive() external payable {
        if (accept) return;

        // Burn past the 50_000-gas forward with cold SSTOREs; never reverts, just runs the sub-call out
        // of gas so the gas-capped caller observes success == false.
        for (uint256 i = 0; i < 64; ++i) {
            _sink[i] = i + 1;
        }
    }
}

/// @dev MockERC20 whose `transfer` returns false (never reverts) only when the recipient is `denied`;
///      every other recipient is paid normally on the same rail. The per-recipient denylist lets one
///      payee be hostile while a disjoint payee is paid in full on the same token, so cross-party
///      no-strand is observable on the ERC-20 rail. `transferFrom` always succeeds so deposits and bond
///      pulls work.
contract H_DenylistERC20 is MockERC20 {
    address public denied;

    constructor() MockERC20("Denylist USD", "dUSD", 6) {}

    function setDenied(address who) external {
        denied = who;
    }

    function transfer(address to, uint256 value) public override returns (bool) {
        if (to == denied) return false; // false return parks the payout to this recipient

        return super.transfer(to, value);
    }
}

/// @dev Hostile BUYER for the native refund terminals: as the lot principal/highBidder it is the refund
///      push target. `receive()` reverts while `reject` is true, so the gas-capped native push parks the
///      refund; toggle `reject` off for `claimPending`. Being a contract principal routes placeBid
///      signature checks to ERC-1271, and `isValidSignature` returns the magic value for any signature,
///      so the ceiling-signing helper authorizes this contract as bidder.
contract H_HostileBuyer is IERC1271 {
    bool public reject = true;

    function setReject(bool v) external {
        reject = v;
    }

    /// @dev ERC-1271: accept every signature (magic value), so the contract can be the bid principal.
    function isValidSignature(bytes32, bytes calldata) external view override returns (bytes4) {
        return IERC1271.isValidSignature.selector; // 0x1626ba7e
    }

    receive() external payable {
        if (reject) revert("no ether");
    }
}

contract DenominationTest is HammerBase {
    // EIP-712 domain constants for the clone (constructor EIP712("Hammer","1")).
    bytes32 private constant EIP712_TYPE_HASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");
    bytes32 private constant HASHED_NAME = keccak256(bytes("Hammer"));
    bytes32 private constant HASHED_VERSION = keccak256(bytes("1"));

    uint256 private constant LOT = 1;

    // bidder1's signing key (the makeAddr("bidder1") address from HammerBase.setUp).
    uint256 private bidder1Key;

    // Proportional amounts per rail: native 1e18 base, ERC-20 1e6 base (6 dp). Every ratio is identical,
    // so "equal modulo decimals" is a pure scale by 1e12.
    uint256 private constant NATIVE_RESERVE = 1 ether; // == RESERVE_PRICE
    uint256 private constant NATIVE_DEPOSIT = 10 ether; // slack hides the ceiling
    uint128 private constant NATIVE_BID = 4 ether; // winning public bid

    uint256 private constant TOKEN_RESERVE = 1e6; // 1.000000 mUSD
    uint256 private constant TOKEN_DEPOSIT = 10e6;
    uint128 private constant TOKEN_BID = 4e6;

    // The dispute bond (DISPUTE_BOND_AMT == 0.1 ether == 1e17 base units) is large in 6-dp token units,
    // so hostile-token actors are minted well above deposit + bond + slack to cover both the deposit and
    // the openDispute bond safeTransferFrom.
    uint256 private constant HOSTILE_TOKEN_MINT = uint256(DISPUTE_BOND_AMT) * 4 + TOKEN_DEPOSIT * 4;

    function setUp() public override {
        super.setUp();
        (, bidder1Key) = makeAddrAndKey("bidder1");
    }

    // Full happy path identical on both rails (proceeds, fee, escrow, slack equal modulo decimals).
    function test_DenominationParityHappyPath() public {
        // Native rail.
        (uint256 nProceeds, uint256 nFee, uint256 nSlack, uint256 nEscrow) =
            _runHappyPathAndMeasure(address(0), NATIVE_RESERVE, NATIVE_DEPOSIT, NATIVE_BID);

        // ERC-20 rail (6 decimals).
        (uint256 tProceeds, uint256 tFee, uint256 tSlack, uint256 tEscrow) =
            _runHappyPathAndMeasure(address(token), TOKEN_RESERVE, TOKEN_DEPOSIT, TOKEN_BID);

        // Identical accounting modulo the 1e12 decimal scale (18 dp native vs 6 dp token).
        uint256 scale = 1e12;
        assertEq(nEscrow, tEscrow * scale, "escrow not equal modulo decimals");
        assertEq(nProceeds, tProceeds * scale, "proceeds not equal modulo decimals");
        assertEq(nFee, tFee * scale, "fee not equal modulo decimals");
        assertEq(nSlack, tSlack * scale, "slack not equal modulo decimals");

        // Fee is FEE_BPS of escrow and proceeds is the remainder on each rail (no rail drift).
        assertEq(nFee, (nEscrow * FEE_BPS) / 10_000, "native fee != feeBps of escrow");
        assertEq(nProceeds, nEscrow - nFee, "native proceeds != escrow - fee");
        assertEq(tFee, (tEscrow * FEE_BPS) / 10_000, "token fee != feeBps of escrow");
        assertEq(tProceeds, tEscrow - tFee, "token proceeds != escrow - fee");
    }

    /// @dev Drive one rail end to end and return (proceeds, fee, slack, escrow), deterministic from the
    ///      bid + feeBps, for the cross-rail parity comparison.
    function _runHappyPathAndMeasure(address paymentToken, uint256 reserve, uint256 deposit, uint128 bid)
        private
        returns (uint256 proceeds, uint256 fee, uint256 slack, uint256 escrow)
    {
        SessionAuction a = _initAuction(paymentToken);

        _openLot(a, paymentToken, uint96(reserve));
        _deposit(a, paymentToken, bidder1, deposit);
        _placeWinningBid(a, paymentToken, bidder1, bid);
        _hammer(a);
        _commitBidBook(a);
        _finalize(a, bid);
        _markDelivered(a);

        escrow = uint256(bid);
        fee = (escrow * FEE_BPS) / 10_000; // Math.mulDiv floor (FEE_BPS == 250)
        proceeds = escrow - fee; // dust (none here) stays with seller
        slack = deposit - uint256(bid); // free reclaimable after the bid committed

        uint256 sellerBefore = _bal(paymentToken, seller);
        uint256 feeRecvBefore = _bal(paymentToken, houseFeeRecipient);

        // Buyer-confirmation event then the inner Released, with exact proceeds/fee.
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Confirmed(LOT, keccak256("photo"), "ipfs://photo");
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT, seller, proceeds, fee);

        vm.prank(bidder1);
        a.confirmReceipt(LOT, keccak256("photo"), "ipfs://photo"); // Delivered -> Released (_release)

        Lot memory lot = a.getLot(LOT);
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "phase != Settled");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Released), "deliveryState != Released");
        assertEq(uint256(lot.escrowAmount), 0, "escrow not zeroed");
        assertEq(_bal(paymentToken, seller) - sellerBefore, proceeds, "seller not paid proceeds");
        assertEq(_bal(paymentToken, houseFeeRecipient) - feeRecvBefore, fee, "feeRecipient not paid fee");
        assertEq(a.withdrawableFree(LOT, bidder1), slack, "slack not reclaimable as free");

        // Actually withdraw the slack so the freed-slack payout runs per rail (native push vs ERC-20
        // transfer of the freed amount), not merely accounted in the free bucket.
        uint256 bidderBeforeWithdraw = _bal(paymentToken, bidder1);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.DepositWithdrawn(LOT, bidder1, slack);

        vm.prank(bidder1);
        a.withdrawDeposit(LOT, slack);

        assertEq(_bal(paymentToken, bidder1) - bidderBeforeWithdraw, slack, "slack not paid out on withdraw");
        assertEq(a.withdrawableFree(LOT, bidder1), 0, "free not zeroed after slack withdraw");
    }

    // Every settlement payout path works on both rails; escrow + bond conserved per rail.
    function test_D5PayoutMatrixBothRails() public {
        // Equal modulo decimals on every payout path, not just confirmReceipt. Each non-confirm helper
        // returns its measured amounts for the same native == token*1e12 check; a rail-specific drift
        // would pass per-rail conservation yet break this cross-rail comparison.
        uint256 scale = 1e12;

        // confirmReceipt path: conservation only (test_DenominationParityHappyPath owns its cross-rail parity).
        _confirmReceiptRail(address(0), NATIVE_DEPOSIT, NATIVE_BID);
        _confirmReceiptRail(address(token), TOKEN_DEPOSIT, TOKEN_BID);

        // auto-release: parity of (escrow, proceeds, fee) across rails.
        (uint256 nEscrowAR, uint256 nProceedsAR, uint256 nFeeAR) =
            _autoReleaseRail(address(0), NATIVE_DEPOSIT, NATIVE_BID);
        (uint256 tEscrowAR, uint256 tProceedsAR, uint256 tFeeAR) =
            _autoReleaseRail(address(token), TOKEN_DEPOSIT, TOKEN_BID);
        assertEq(nEscrowAR, tEscrowAR * scale, "auto-release escrow not equal modulo decimals");
        assertEq(nProceedsAR, tProceedsAR * scale, "auto-release proceeds not equal modulo decimals");
        assertEq(nFeeAR, tFeeAR * scale, "auto-release fee not equal modulo decimals");

        // reclaim/refund: the refund pays the FULL escrow with NO fee on both rails (parity of refund).
        uint256 nRefundRC = _reclaimUndeliveredRail(address(0), NATIVE_DEPOSIT, NATIVE_BID);
        uint256 tRefundRC = _reclaimUndeliveredRail(address(token), TOKEN_DEPOSIT, TOKEN_BID);
        assertEq(nRefundRC, uint256(NATIVE_BID), "reclaim native refund != full escrow (fee leaked)");
        assertEq(tRefundRC, uint256(TOKEN_BID), "reclaim token refund != full escrow (fee leaked)");
        assertEq(nRefundRC, tRefundRC * scale, "reclaim refund not equal modulo decimals");

        // dispute-release: parity of (proceeds, fee, bondOut) value-OUT and bondIn value-IN (the bond
        // debited from the opener). Opener is the BUYER.
        (uint256 nProceedsDR, uint256 nFeeDR, uint256 nBondDR, uint256 nBondInDR) =
            _disputeReleaseRail(address(0), NATIVE_DEPOSIT, NATIVE_BID);
        (uint256 tProceedsDR, uint256 tFeeDR, uint256 tBondDR, uint256 tBondInDR) =
            _disputeReleaseRail(address(token), TOKEN_DEPOSIT, TOKEN_BID);
        assertEq(nProceedsDR, tProceedsDR * scale, "dispute-release proceeds not equal modulo decimals");
        assertEq(nFeeDR, tFeeDR * scale, "dispute-release fee not equal modulo decimals");

        // The bond is a flat base-unit amount (DISPUTE_BOND_AMT regardless of paymentToken), so unlike the
        // bid-derived amounts it is identical on both rails, NOT scaled by 1e12. Asserting
        // nBondDR == tBondDR*1e12 (1e17 == 1e29) would reject a correct flat bond.
        assertEq(nBondDR, tBondDR, "dispute-release bond not equal (flat, not scaled by decimals)");
        assertEq(nBondDR, uint256(DISPUTE_BOND_AMT), "dispute-release bond != flat DISPUTE_BOND_AMT");

        // IN-leg cross-rail parity: the bond debited from the opener is the same flat amount on both rails
        // (native msg.value, ERC-20 safeTransferFrom), symmetric to the value-OUT parity.
        assertEq(nBondInDR, tBondInDR, "dispute-release bond IN not equal (flat, not scaled by decimals)");
        assertEq(nBondInDR, uint256(DISPUTE_BOND_AMT), "dispute-release bond IN != flat DISPUTE_BOND_AMT");

        // Round-trip closure: the flat bond that entered (IN) is the one paid OUT to the honest party.
        assertEq(nBondInDR, nBondDR, "dispute-release native bond IN != bond OUT (bond not conserved)");
        assertEq(tBondInDR, tBondDR, "dispute-release token bond IN != bond OUT (bond not conserved)");

        // dispute-refund: parity of (refund, bondOut) value-OUT and bondIn value-IN; refund is the full
        // escrow with no fee on both. Opener is the SELLER (symmetric to dispute-release).
        (uint256 nRefundDF, uint256 nBondDF, uint256 nBondInDF) =
            _disputeRefundRail(address(0), NATIVE_DEPOSIT, NATIVE_BID);
        (uint256 tRefundDF, uint256 tBondDF, uint256 tBondInDF) =
            _disputeRefundRail(address(token), TOKEN_DEPOSIT, TOKEN_BID);
        assertEq(nRefundDF, uint256(NATIVE_BID), "dispute-refund native refund != full escrow (fee leaked)");
        assertEq(tRefundDF, uint256(TOKEN_BID), "dispute-refund token refund != full escrow (fee leaked)");
        assertEq(nRefundDF, tRefundDF * scale, "dispute-refund refund not equal modulo decimals");

        // Flat bond on the refund path too: identical on both rails, not scaled.
        assertEq(nBondDF, tBondDF, "dispute-refund bond not equal (flat, not scaled by decimals)");
        assertEq(nBondDF, uint256(DISPUTE_BOND_AMT), "dispute-refund bond != flat DISPUTE_BOND_AMT");

        // IN-leg cross-rail parity for a SELLER opener, round-tripping to the bond paid OUT.
        assertEq(nBondInDF, tBondInDF, "dispute-refund bond IN not equal (flat, not scaled by decimals)");
        assertEq(nBondInDF, uint256(DISPUTE_BOND_AMT), "dispute-refund bond IN != flat DISPUTE_BOND_AMT");
        assertEq(nBondInDF, nBondDF, "dispute-refund native bond IN != bond OUT (bond not conserved)");
        assertEq(tBondInDF, tBondDF, "dispute-refund token bond IN != bond OUT (bond not conserved)");

        // Cross-path IN-leg parity: a BUYER opener (release path) and a SELLER opener (refund path) are
        // debited the same flat bond on each rail, so the IN-leg is opener-symmetric, not just rail-symmetric.
        assertEq(nBondInDR, nBondInDF, "native: buyer-opener bond IN != seller-opener bond IN");
        assertEq(tBondInDR, tBondInDF, "token: buyer-opener bond IN != seller-opener bond IN");
    }

    /// @dev releaseAfterWindow (auto-release): Delivered -> Released after disputeWindowSec. Returns the
    ///      measured (escrow, proceeds, fee) moved out of the clone for cross-rail parity. Warps off the
    ///      STORED `deliveredAt` (not block.timestamp + window).
    function _autoReleaseRail(address paymentToken, uint256 deposit, uint128 bid)
        private
        returns (uint256 escrow, uint256 proceeds, uint256 fee)
    {
        SessionAuction a = _freshDeliveredLot(paymentToken, deposit, bid);

        escrow = uint256(bid);
        fee = (escrow * FEE_BPS) / 10_000;
        proceeds = escrow - fee;

        // Reference state written by markDelivered, pinned per rail.
        uint256 deliveredAt = uint256(a.getLot(LOT).deliveredAt);
        assertEq(deliveredAt, block.timestamp, "auto-release: deliveredAt != mark time");
        assertEq(a.getLot(LOT).deliveryProofHash, keccak256("delivery-proof"), "auto-release: proof hash not stored");

        uint256 cloneBefore = _bal(paymentToken, address(a));
        uint256 sellerBefore = _bal(paymentToken, seller);
        uint256 feeRecvBefore = _bal(paymentToken, houseFeeRecipient);
        uint256 escrowHeldBefore = uint256(a.getLot(LOT).escrowAmount); // conserved bucket
        assertEq(escrowHeldBefore, escrow, "escrow not held pre-release");

        vm.warp(deliveredAt + DISPUTE_WINDOW_SEC); // exactly at deliveredAt + disputeWindowSec

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.DeliveryAutoReleased(LOT, seller);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT, seller, proceeds, fee);

        a.releaseAfterWindow(LOT); // permissionless

        Lot memory lot = a.getLot(LOT);
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "auto-release phase != Settled");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Released), "auto-release deliveryState != Released");
        assertEq(uint256(lot.escrowAmount), 0, "auto-release escrow not zeroed");

        // Conservation: escrow leaves the clone in full (proceeds + fee == escrow).
        assertEq(proceeds + fee, escrow, "proceeds+fee != escrow");
        assertEq(cloneBefore - _bal(paymentToken, address(a)), escrow, "clone balance delta != escrow");

        // Measured payouts: the source of the returned parity values.
        assertEq(_bal(paymentToken, seller) - sellerBefore, proceeds, "auto-release seller != proceeds");
        assertEq(_bal(paymentToken, houseFeeRecipient) - feeRecvBefore, fee, "auto-release feeRecipient != fee");

        // No double-pay: a repeat on an already-Released lot fails the deliveryState == Delivered guard and
        // reverts WrongDeliveryState before any release; the clone balance is unchanged.
        uint256 cloneAfter = _bal(paymentToken, address(a));
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        a.releaseAfterWindow(LOT);
        assertEq(_bal(paymentToken, address(a)), cloneAfter, "auto-release: second call moved funds");
    }

    /// @dev confirmReceipt: Delivered -> Released; SUM(escrow) conserved (proceeds + fee == escrow).
    function _confirmReceiptRail(address paymentToken, uint256 deposit, uint128 bid) private {
        SessionAuction a = _freshDeliveredLot(paymentToken, deposit, bid);

        uint256 escrow = uint256(bid);
        uint256 fee = (escrow * FEE_BPS) / 10_000;
        uint256 proceeds = escrow - fee;
        uint256 slack = deposit - uint256(bid); // bidder1 free, held by the clone throughout
        uint256 cloneBefore = _bal(paymentToken, address(a));

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT, seller, proceeds, fee);

        vm.prank(bidder1);
        a.confirmReceipt(LOT, bytes32(0), "");

        assertEq(uint256(a.getLot(LOT).escrowAmount), 0, "confirm escrow not zeroed");
        assertEq(cloneBefore - _bal(paymentToken, address(a)), escrow, "confirm clone delta != escrow");

        // Conservation tied to the internal accounting buckets, not just balanceOf: the residual clone
        // balance is the bidder's free, still owned by the bidder.
        assertEq(_bal(paymentToken, address(a)), slack, "confirm clone residual != slack");
        assertEq(a.withdrawableFree(LOT, bidder1), slack, "confirm free bucket != slack");

        // No double-pay: a second confirmReceipt sees deliveryState == Released and reverts
        // WrongDeliveryState before any release; the residual (the bidder's slack) is untouched.
        uint256 cloneAfter = _bal(paymentToken, address(a));
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        a.confirmReceipt(LOT, bytes32(0), "");
        assertEq(_bal(paymentToken, address(a)), cloneAfter, "confirm: second call moved funds");
    }

    /// @dev reclaimUndelivered: AwaitingDelivery -> Refunded after sellerDeliverSec; full escrow, no fee,
    ///      to the buyer. Returns the measured refund (buyer balance delta) for the cross-rail parity
    ///      check. Warps off the STORED `awaitingAt`.
    function _reclaimUndeliveredRail(address paymentToken, uint256 deposit, uint128 bid)
        private
        returns (uint256 refund)
    {
        SessionAuction a = _freshAwaitingLot(paymentToken, deposit, bid);

        uint256 escrow = uint256(bid);
        uint256 cloneBefore = _bal(paymentToken, address(a));
        uint256 buyerBefore = _bal(paymentToken, bidder1);

        // awaitingAt is set by finalizeWinner; warp off the STORED value.
        uint256 awaitingAt = uint256(a.getLot(LOT).awaitingAt);
        assertEq(awaitingAt, block.timestamp, "reclaim: awaitingAt != finalize time");
        vm.warp(awaitingAt + SELLER_DELIVER_SEC); // exactly at awaitingAt + sellerDeliverSec

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.ReclaimedUndelivered(LOT, bidder1, bid);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Refunded(LOT, bidder1, escrow);

        vm.prank(bidder1);
        a.reclaimUndelivered(LOT);

        Lot memory lot = a.getLot(LOT);
        assertEq(uint8(lot.phase), uint8(LotPhase.Refunded), "reclaim phase != Refunded");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Refunded), "reclaim deliveryState != Refunded");
        assertEq(uint256(lot.escrowAmount), 0, "reclaim escrow not zeroed");
        refund = _bal(paymentToken, bidder1) - buyerBefore;
        assertEq(refund, escrow, "buyer not refunded full escrow");
        assertEq(cloneBefore - _bal(paymentToken, address(a)), escrow, "reclaim clone delta != escrow");

        // No double-pay: a second reclaim sees deliveryState == Refunded and reverts WrongDeliveryState
        // before any refund; the clone balance (the bidder's still-held slack) is unchanged.
        uint256 cloneAfter = _bal(paymentToken, address(a));
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        a.reclaimUndelivered(LOT);
        assertEq(_bal(paymentToken, address(a)), cloneAfter, "reclaim: second call moved funds");
    }

    /// @dev openDispute (buyer) then resolveDispute(ReleaseToSeller): bond returns to the honest
    ///      party (seller, since opener is the buyer and loses), escrow released. SUM(escrow+bond)
    ///      conserved across the two-step path.
    function _disputeReleaseRail(address paymentToken, uint256 deposit, uint128 bid)
        private
        returns (uint256 proceeds, uint256 fee, uint256 bondOut, uint256 bondIn)
    {
        SessionAuction a = _freshDeliveredLot(paymentToken, deposit, bid);

        // On the token rail the opener (buyer) holds only INITIAL_TOKEN == 1e12 minus its deposit, far
        // below the flat 1e17 bond, so the bond safeTransferFrom would revert ERC20InsufficientBalance.
        // Mint enough to cover it; the bond stays flat 1e17 on the token rail (not scaled).
        if (paymentToken == address(token)) token.mint(bidder1, DISPUTE_BOND_AMT);

        uint256 escrow = uint256(bid);
        fee = (escrow * FEE_BPS) / 10_000;
        proceeds = escrow - fee;
        uint256 bond = uint256(DISPUTE_BOND_AMT);
        uint256 slack = deposit - uint256(bid); // bidder1 free still held by the clone throughout

        uint256 cloneBeforeOpen = _bal(paymentToken, address(a));
        assertEq(cloneBeforeOpen, escrow + slack, "pre-open clone != escrow + slack");

        // Buyer opens the dispute, bonding the bond (native msg.value; ERC-20 pull). The helper pins the
        // opener-side debit; `bondIn` is returned for the cross-rail value-IN parity check.
        (uint256 cloneAfterOpen, uint256 openerOut) = _openDisputeAs(a, paymentToken, bidder1, bond);
        bondIn = openerOut;

        // Only the bond is pulled IN; escrow and bond are disjoint pools held side by side. The clone delta
        // alone cannot prove the bond came FROM the opener (a mis-sourced pull would still satisfy it), so
        // pin the opener debit too.
        assertEq(cloneAfterOpen - cloneBeforeOpen, bond, "openDispute pulled != bond");
        assertEq(openerOut, bond, "dispute-release: opener (buyer) not debited exactly the bond");

        Lot memory mid = a.getLot(LOT);
        assertEq(uint8(mid.deliveryState), uint8(DeliveryState.Disputed), "not Disputed after open");
        assertEq(uint256(mid.disputeBond), bond, "stored bond != pulled bond");
        assertEq(mid.disputeOpener, bidder1, "dispute-release: disputeOpener != buyer");
        assertEq(mid.disputeRef, keccak256("claim"), "dispute-release: disputeRef not stored");

        uint256 sellerBefore = _bal(paymentToken, seller);
        uint256 feeRecvBefore = _bal(paymentToken, houseFeeRecipient);

        // Arbiter resolves to the seller; opener (buyer) LOSES so the bond goes to the seller.
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT, seller, proceeds, fee);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.DisputeResolved(LOT, Resolution.ReleaseToSeller, seller);

        vm.prank(arbiter);
        a.resolveDispute(LOT, Resolution.ReleaseToSeller, bytes32(0));

        Lot memory lot = a.getLot(LOT);
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "dispute-release phase != Settled");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Released), "dispute-release deliveryState != Released");
        assertEq(uint256(lot.escrowAmount), 0, "dispute-release escrow not zeroed");
        assertEq(uint256(lot.disputeBond), 0, "dispute-release bond not zeroed");

        // Conservation: exactly escrow + bond leaves the clone; the slack stays held as free.
        assertEq(cloneAfterOpen - _bal(paymentToken, address(a)), escrow + bond, "clone delta != escrow + bond");
        assertEq(_bal(paymentToken, address(a)), slack, "clone residual != slack");
        assertEq(a.withdrawableFree(LOT, bidder1), slack, "dispute-release free bucket != slack");

        // Seller (honest party, opener lost) receives proceeds + bond; the fee goes to the recipient.
        assertEq(_bal(paymentToken, seller) - sellerBefore, proceeds + bond, "seller payout != proceeds + bond");
        assertEq(_bal(paymentToken, houseFeeRecipient) - feeRecvBefore, fee, "feeRecipient != fee");
        bondOut = bond; // the bond paid OUT, returned as the parity quantity
    }

    /// @dev openDispute (seller) then resolveDispute(RefundToBuyer): opener (seller) LOSES, bond to
    ///      the buyer (honest party), full escrow refunded to the buyer. SUM(escrow+bond) conserved.
    function _disputeRefundRail(address paymentToken, uint256 deposit, uint128 bid)
        private
        returns (uint256 refund, uint256 bondOut, uint256 bondIn)
    {
        SessionAuction a = _freshDeliveredLot(paymentToken, deposit, bid);

        // Mint the bond for the opener, here the SELLER (same flat-1e17-bond underfunding as
        // _disputeReleaseRail: the seller holds only INITIAL_TOKEN == 1e12 on the token rail).
        if (paymentToken == address(token)) token.mint(seller, DISPUTE_BOND_AMT);

        uint256 escrow = uint256(bid);
        uint256 bond = uint256(DISPUTE_BOND_AMT);
        uint256 slack = deposit - uint256(bid);

        uint256 cloneBeforeOpen = _bal(paymentToken, address(a));

        // SELLER opens then loses on RefundToBuyer. The helper pins the opener-side debit on whichever
        // party opens, so IN-leg parity is proven for a SELLER opener too, not only a buyer opener.
        (uint256 cloneAfterOpen, uint256 openerOut) = _openDisputeAs(a, paymentToken, seller, bond);
        bondIn = openerOut;
        assertEq(cloneAfterOpen - cloneBeforeOpen, bond, "seller openDispute pulled != bond");
        assertEq(openerOut, bond, "dispute-refund: opener (seller) not debited exactly the bond");

        Lot memory mid = a.getLot(LOT);
        assertEq(mid.disputeOpener, seller, "dispute-refund: disputeOpener != seller");
        assertEq(mid.disputeRef, keccak256("claim"), "dispute-refund: disputeRef not stored");

        uint256 buyerBefore = _bal(paymentToken, bidder1);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Refunded(LOT, bidder1, escrow);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.DisputeResolved(LOT, Resolution.RefundToBuyer, bidder1);

        vm.prank(arbiter);
        a.resolveDispute(LOT, Resolution.RefundToBuyer, bytes32(0));

        Lot memory lot = a.getLot(LOT);
        assertEq(uint8(lot.phase), uint8(LotPhase.Refunded), "dispute-refund phase != Refunded");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Refunded), "dispute-refund deliveryState != Refunded");
        assertEq(uint256(lot.escrowAmount), 0, "dispute-refund escrow not zeroed");
        assertEq(uint256(lot.disputeBond), 0, "dispute-refund bond not zeroed");

        // Conservation: escrow + bond leave, slack remains. Buyer (honest party + refundee) gets both.
        assertEq(cloneAfterOpen - _bal(paymentToken, address(a)), escrow + bond, "clone delta != escrow + bond");
        assertEq(_bal(paymentToken, address(a)), slack, "clone residual != slack");
        assertEq(a.withdrawableFree(LOT, bidder1), slack, "dispute-refund free bucket != slack");
        assertEq(_bal(paymentToken, bidder1) - buyerBefore, escrow + bond, "buyer payout != escrow + bond");

        // The two returned parity quantities: the refund (full escrow, no fee) and the bond.
        refund = escrow;
        bondOut = bond;
    }

    // Hostile payee no-strand on both rails: parked to pending withdrawals, claimPending pulls.

    /// @dev Native rail: the seller reverts on receive, so the gas-capped push fails and `proceeds` is
    ///      credited to pending withdrawals; the terminal still completes, the feeRecipient is paid, and
    ///      claimPending later pulls the parked proceeds.
    function test_HostilePayeeNoStrandBothRails() public {
        // Native rail: hostile SELLER (reverting receiver).
        H_RejectingReceiver hostileSeller = new H_RejectingReceiver();
        SessionAuction an = _freshDeliveredLotWithSeller(address(0), NATIVE_DEPOSIT, NATIVE_BID, address(hostileSeller));

        uint256 escrowN = uint256(NATIVE_BID);
        uint256 feeN = (escrowN * FEE_BPS) / 10_000;
        uint256 proceedsN = escrowN - feeN;
        uint256 slackN = NATIVE_DEPOSIT - escrowN; // bidder1 free, held by the clone throughout
        uint256 feeRecvBefore = houseFeeRecipient.balance;

        // Physical-hold snapshot: the clone must still hold the parked value, not merely credit the
        // ledger. A credit-but-mis-forward (a send to the wrong target) passes the pendingWithdrawal
        // check but fails this balance pin.
        uint256 cloneBeforeN = address(an).balance;
        assertEq(cloneBeforeN, escrowN + slackN, "native hostile: pre-terminal clone != escrow + slack");

        // The unpayable proceeds are credited, not reverted; the fee recipient is still paid.
        vm.expectEmit(true, true, true, true, address(an));
        emit ISessionAuction.WithdrawalCredited(address(hostileSeller), proceedsN);
        vm.expectEmit(true, true, true, true, address(an));
        emit ISessionAuction.Released(LOT, address(hostileSeller), proceedsN, feeN);

        vm.prank(bidder1);
        an.confirmReceipt(LOT, bytes32(0), ""); // Delivered -> Released, push to seller fails -> park

        Lot memory ln = an.getLot(LOT);
        assertEq(uint8(ln.phase), uint8(LotPhase.Settled), "native hostile: phase != Settled");
        assertEq(uint256(ln.escrowAmount), 0, "native hostile: escrow not zeroed");
        assertEq(an.pendingWithdrawal(address(hostileSeller)), proceedsN, "native hostile: proceeds not parked");
        assertEq(houseFeeRecipient.balance - feeRecvBefore, feeN, "native hostile: feeRecipient not paid");

        // Only the fee left (to the healthy recipient): the clone still holds the parked proceeds plus the
        // bidder's slack, pinning the parked value to the contract.
        assertEq(address(an).balance, proceedsN + slackN, "native hostile: clone not holding parked proceeds + slack");
        assertEq(cloneBeforeN - address(an).balance, feeN, "native hostile: only the fee should have left the clone");

        // Toggle the receiver to accept, then claimPending pulls the parked proceeds out to it.
        hostileSeller.setReject(false);
        uint256 sellerEthBefore = address(hostileSeller).balance;
        uint256 cloneBeforeClaimN = address(an).balance;

        vm.expectEmit(true, true, true, true, address(an));
        emit ISessionAuction.WithdrawalClaimed(address(hostileSeller), proceedsN);
        vm.prank(address(hostileSeller));
        an.claimPending();

        assertEq(an.pendingWithdrawal(address(hostileSeller)), 0, "native hostile: pending not cleared");
        assertEq(address(hostileSeller).balance - sellerEthBefore, proceedsN, "native hostile: not paid on claim");

        // claimPending drops the clone by exactly the parked proceeds, leaving only the bidder's slack.
        assertEq(cloneBeforeClaimN - address(an).balance, proceedsN, "native hostile: claim moved != parked proceeds");
        assertEq(address(an).balance, slackN, "native hostile: post-claim clone residual != slack");

        // ERC-20 rail: token whose transfer() returns false until toggled.
        H_FalseReturningERC20 badToken = new H_FalseReturningERC20();
        badToken.mint(bidder1, INITIAL_TOKEN);
        badToken.mint(seller, INITIAL_TOKEN);

        SessionAuction at = _initAuction(address(badToken));
        _openLot(at, address(badToken), uint96(TOKEN_RESERVE));
        _deposit(at, address(badToken), bidder1, TOKEN_DEPOSIT); // transferFrom always succeeds, deposit OK
        _placeWinningBid(at, address(badToken), bidder1, TOKEN_BID);
        _hammer(at);
        _commitBidBook(at);
        _finalize(at, TOKEN_BID);
        _markDelivered(at);

        uint256 escrowT = uint256(TOKEN_BID);
        uint256 feeT = (escrowT * FEE_BPS) / 10_000;
        uint256 proceedsT = escrowT - feeT;
        uint256 slackT = TOKEN_DEPOSIT - escrowT; // bidder1 free, held by the clone throughout

        // Physical-hold snapshot, ERC-20 rail. With a globally-failing token both payout legs park, so no
        // token leaves the clone at terminal time; it must still hold the full escrow + slack.
        uint256 cloneBeforeT = badToken.balanceOf(address(at));
        assertEq(cloneBeforeT, escrowT + slackT, "token hostile: pre-terminal clone != escrow + slack");

        // transfer returns false, so both payout legs (seller proceeds, then feeRecipient fee) credit
        // pending withdrawals rather than revert; the terminal still completes (a false return is observed
        // and parked, never reverted).
        vm.expectEmit(true, true, true, true, address(at));
        emit ISessionAuction.WithdrawalCredited(seller, proceedsT);
        vm.expectEmit(true, true, true, true, address(at));
        emit ISessionAuction.WithdrawalCredited(houseFeeRecipient, feeT);
        vm.expectEmit(true, true, true, true, address(at));
        emit ISessionAuction.Released(LOT, seller, proceedsT, feeT);

        vm.prank(bidder1);
        at.confirmReceipt(LOT, bytes32(0), "");

        Lot memory lt = at.getLot(LOT);
        assertEq(uint8(lt.phase), uint8(LotPhase.Settled), "token hostile: phase != Settled");
        assertEq(uint256(lt.escrowAmount), 0, "token hostile: escrow not zeroed");
        assertEq(at.pendingWithdrawal(seller), proceedsT, "token hostile: seller proceeds not parked");
        assertEq(at.pendingWithdrawal(houseFeeRecipient), feeT, "token hostile: fee not parked");

        // Nothing transferred: the clone still holds the entire escrow (proceeds + fee) plus the bidder's
        // slack, unchanged from before the terminal.
        assertEq(badToken.balanceOf(address(at)), escrowT + slackT, "token hostile: clone not holding parked escrow + slack");
        assertEq(badToken.balanceOf(address(at)), cloneBeforeT, "token hostile: token wrongly left the clone at park time");

        // Toggle the token healthy, then claimPending pulls the parked proceeds to the seller.
        badToken.setFail(false);
        uint256 sellerBalBefore = badToken.balanceOf(seller);
        uint256 cloneBeforeClaimT = badToken.balanceOf(address(at));

        vm.expectEmit(true, true, true, true, address(at));
        emit ISessionAuction.WithdrawalClaimed(seller, proceedsT);
        vm.prank(seller);
        at.claimPending();

        assertEq(at.pendingWithdrawal(seller), 0, "token hostile: seller pending not cleared");
        assertEq(badToken.balanceOf(seller) - sellerBalBefore, proceedsT, "token hostile: seller not paid on claim");

        // claimPending drops the clone by exactly the seller's parked proceeds; the still-parked fee and
        // the bidder's slack remain.
        assertEq(cloneBeforeClaimT - badToken.balanceOf(address(at)), proceedsT, "token hostile: claim moved != parked proceeds");
        assertEq(badToken.balanceOf(address(at)), slackT + feeT, "token hostile: post-claim clone != slack + still-parked fee");
        assertEq(at.pendingWithdrawal(houseFeeRecipient), feeT, "token hostile: fee pending changed by seller claim");
    }

    // Native push gas cap: the push forwards only 50_000 gas, so a payee that does not revert but burns
    // more than the cap must still fall through to the pending credit (an uncapped send forwards all gas).
    function test_HostileSellerGasGuzzler_Native() public {
        H_GasGuzzlerReceiver guzzler = new H_GasGuzzlerReceiver();
        vm.deal(address(guzzler), INITIAL_ETH); // never sends, funded for symmetry
        SessionAuction a = _freshDeliveredLotWithSeller(address(0), NATIVE_DEPOSIT, NATIVE_BID, address(guzzler));

        uint256 escrow = uint256(NATIVE_BID);
        uint256 fee = (escrow * FEE_BPS) / 10_000;
        uint256 proceeds = escrow - fee;
        uint256 feeRecvBefore = houseFeeRecipient.balance;

        // The guzzler consumes the whole 50_000-gas forward so the push returns success == false; proceeds
        // park (not revert), the fee recipient is paid, the terminal completes.
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(address(guzzler), proceeds);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT, address(guzzler), proceeds, fee);

        vm.prank(bidder1);
        a.confirmReceipt(LOT, bytes32(0), "");

        Lot memory lot = a.getLot(LOT);
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "guzzler: phase != Settled");
        assertEq(uint256(lot.escrowAmount), 0, "guzzler: escrow not zeroed");
        assertEq(
            a.pendingWithdrawal(address(guzzler)), proceeds, "guzzler: proceeds not parked (gas cap not enforced?)"
        );
        assertEq(houseFeeRecipient.balance - feeRecvBefore, fee, "guzzler: feeRecipient not paid");

        // Stop guzzling, then claimPending pulls the parked proceeds (claim is uncapped).
        guzzler.setAccept(true);
        uint256 guzzlerBefore = address(guzzler).balance;

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalClaimed(address(guzzler), proceeds);
        vm.prank(address(guzzler));
        a.claimPending();

        assertEq(a.pendingWithdrawal(address(guzzler)), 0, "guzzler: pending not cleared");
        assertEq(address(guzzler).balance - guzzlerBefore, proceeds, "guzzler: not paid on claim");
    }

    // Hostile BUYER on the refund terminals: reclaimUndelivered and resolveDispute(RefundToBuyer) both
    // refund the buyer, which must park (not revert) when the buyer is hostile. Native + ERC-20.

    /// @dev Native: hostile BUYER (reverting ERC-1271 contract) reclaims an undelivered lot; the
    ///      refund push fails and the full escrow is parked, phase Refunded, then claimPending pulls.
    function test_HostileBuyer_Reclaim_Native() public {
        H_HostileBuyer buyer = new H_HostileBuyer();
        SessionAuction a = _freshAwaitingLotWithBuyer(address(0), NATIVE_DEPOSIT, NATIVE_BID, address(buyer));

        uint256 escrow = uint256(NATIVE_BID);
        uint256 slack = NATIVE_DEPOSIT - escrow; // the hostile buyer's own free, held by the clone

        // Physical-hold snapshot on the refund terminal: the clone must still hold the parked refund, not
        // merely credit the ledger.
        uint256 cloneBefore = address(a).balance;
        assertEq(cloneBefore, escrow + slack, "hostile buyer reclaim: pre-terminal clone != escrow + slack");

        vm.warp(block.timestamp + SELLER_DELIVER_SEC); // exactly at awaitingAt + sellerDeliverSec

        // Refund to the hostile buyer fails the push -> parked; the terminal still completes.
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.ReclaimedUndelivered(LOT, address(buyer), NATIVE_BID);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(address(buyer), escrow);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Refunded(LOT, address(buyer), escrow);

        vm.prank(address(buyer));
        a.reclaimUndelivered(LOT);

        Lot memory lot = a.getLot(LOT);
        assertEq(uint8(lot.phase), uint8(LotPhase.Refunded), "hostile buyer reclaim: phase != Refunded");
        assertEq(uint256(lot.escrowAmount), 0, "hostile buyer reclaim: escrow not zeroed");
        assertEq(a.pendingWithdrawal(address(buyer)), escrow, "hostile buyer reclaim: refund not parked");

        // The only payout failed and parked, so the full escrow is still in the clone alongside the
        // buyer's slack; nothing left.
        assertEq(address(a).balance, escrow + slack, "hostile buyer reclaim: clone not holding parked refund + slack");
        assertEq(address(a).balance, cloneBefore, "hostile buyer reclaim: wei wrongly left the clone at park time");

        // Toggle the buyer to accept, claimPending pulls the parked refund.
        buyer.setReject(false);
        uint256 buyerEthBefore = address(buyer).balance;
        uint256 cloneBeforeClaim = address(a).balance;

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalClaimed(address(buyer), escrow);
        vm.prank(address(buyer));
        a.claimPending();

        assertEq(a.pendingWithdrawal(address(buyer)), 0, "hostile buyer reclaim: pending not cleared");
        assertEq(address(buyer).balance - buyerEthBefore, escrow, "hostile buyer reclaim: not paid on claim");

        // claimPending drops the clone by exactly the parked refund, leaving only the buyer's slack (its
        // free bucket, withdrawn separately).
        assertEq(cloneBeforeClaim - address(a).balance, escrow, "hostile buyer reclaim: claim moved != parked refund");
        assertEq(address(a).balance, slack, "hostile buyer reclaim: post-claim clone residual != slack");
    }

    /// @dev ERC-20: hostile BUYER (denylisted EOA, normal in every other respect) reclaims; the
    ///      token transfer to the buyer returns false -> the full escrow is parked, then claimed.
    function test_HostileBuyer_Reclaim_Token() public {
        H_DenylistERC20 dt = new H_DenylistERC20();
        dt.mint(bidder1, HOSTILE_TOKEN_MINT);
        dt.mint(seller, HOSTILE_TOKEN_MINT);

        SessionAuction a = _freshAwaitingLot(address(dt), TOKEN_DEPOSIT, TOKEN_BID);

        uint256 escrow = uint256(TOKEN_BID);
        dt.setDenied(bidder1); // the refund push to the buyer will now return false

        vm.warp(block.timestamp + SELLER_DELIVER_SEC);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.ReclaimedUndelivered(LOT, bidder1, TOKEN_BID);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(bidder1, escrow);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Refunded(LOT, bidder1, escrow);

        vm.prank(bidder1);
        a.reclaimUndelivered(LOT);

        Lot memory lot = a.getLot(LOT);
        assertEq(uint8(lot.phase), uint8(LotPhase.Refunded), "token hostile buyer reclaim: phase != Refunded");
        assertEq(uint256(lot.escrowAmount), 0, "token hostile buyer reclaim: escrow not zeroed");
        assertEq(a.pendingWithdrawal(bidder1), escrow, "token hostile buyer reclaim: refund not parked");

        // Un-deny, then claimPending pulls the parked refund out as a real token transfer.
        dt.setDenied(address(0));
        uint256 buyerBalBefore = dt.balanceOf(bidder1);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalClaimed(bidder1, escrow);
        vm.prank(bidder1);
        a.claimPending();

        assertEq(a.pendingWithdrawal(bidder1), 0, "token hostile buyer reclaim: pending not cleared");
        assertEq(dt.balanceOf(bidder1) - buyerBalBefore, escrow, "token hostile buyer reclaim: not paid on claim");
    }

    /// @dev Native: hostile BUYER on resolveDispute(RefundToBuyer). Opener is the seller (loses), so
    ///      both the escrow refund AND the bond go to the buyer (honest party). Both push to the
    ///      hostile buyer fail -> both park (escrow + bond), then a single claimPending pulls the sum.
    function test_HostileBuyer_DisputeRefund_Native() public {
        H_HostileBuyer buyer = new H_HostileBuyer();
        SessionAuction a = _freshDeliveredLotWithBuyer(address(0), NATIVE_DEPOSIT, NATIVE_BID, address(buyer));

        uint256 escrow = uint256(NATIVE_BID);
        uint256 bond = uint256(DISPUTE_BOND_AMT);

        // Seller opens (honest native EOA), bonds the dispute; opener will LOSE on RefundToBuyer.
        _openDisputeAs(a, address(0), seller, bond);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(address(buyer), escrow); // escrow refund parks
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Refunded(LOT, address(buyer), escrow);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(address(buyer), bond); // bond (honest party) parks
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.DisputeResolved(LOT, Resolution.RefundToBuyer, address(buyer));

        vm.prank(arbiter);
        a.resolveDispute(LOT, Resolution.RefundToBuyer, bytes32(0));

        Lot memory lot = a.getLot(LOT);
        assertEq(uint8(lot.phase), uint8(LotPhase.Refunded), "hostile buyer refund: phase != Refunded");
        assertEq(uint256(lot.escrowAmount), 0, "hostile buyer refund: escrow not zeroed");
        assertEq(uint256(lot.disputeBond), 0, "hostile buyer refund: bond not zeroed");
        // Both the escrow refund and the bond are parked to the same hostile buyer (sum).
        assertEq(a.pendingWithdrawal(address(buyer)), escrow + bond, "hostile buyer refund: escrow+bond not parked");

        buyer.setReject(false);
        uint256 buyerEthBefore = address(buyer).balance;

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalClaimed(address(buyer), escrow + bond);
        vm.prank(address(buyer));
        a.claimPending();

        assertEq(a.pendingWithdrawal(address(buyer)), 0, "hostile buyer refund: pending not cleared");
        assertEq(address(buyer).balance - buyerEthBefore, escrow + bond, "hostile buyer refund: not paid on claim");
    }

    // Hostile dispute-BOND recipient + cross-party no-strand. The bond is its own pool, zeroed before its
    // push, so it must park (not revert) on a hostile recipient. resolveDispute pays the bond and the
    // escrow to the same winning party, so a hostile recipient parks both while the disjoint feeRecipient
    // is paid in full.

    /// @dev Native: ReleaseToSeller with opener == buyer (loses), so the bond AND the release
    ///      proceeds both go to the seller (honest party). The seller is a reverting contract, so
    ///      proceeds + bond both park; the fee (disjoint pool) is paid to feeRecipient normally.
    function test_HostileBondRecipient_Native() public {
        H_RejectingReceiver hostileSeller = new H_RejectingReceiver();
        SessionAuction a = _freshDeliveredLotWithSeller(address(0), NATIVE_DEPOSIT, NATIVE_BID, address(hostileSeller));

        uint256 escrow = uint256(NATIVE_BID);
        uint256 fee = (escrow * FEE_BPS) / 10_000;
        uint256 proceeds = escrow - fee;
        uint256 bond = uint256(DISPUTE_BOND_AMT);
        uint256 slack = NATIVE_DEPOSIT - escrow; // bidder1 free, held by the clone throughout
        uint256 feeRecvBefore = houseFeeRecipient.balance;

        // Buyer opens (honest native EOA); opener LOSES on ReleaseToSeller so the bond goes to the seller.
        _openDisputeAs(a, address(0), bidder1, bond);
        assertEq(uint256(a.getLot(LOT).disputeBond), bond, "bond not stored pre-resolve");

        // Physical-hold snapshot on the bond pool: after the pull the clone holds escrow + slack + bond.
        // Both the escrow release and the bond payout target the hostile seller, so both park yet stay
        // physically in the clone.
        uint256 cloneAfterOpen = address(a).balance;
        assertEq(cloneAfterOpen, escrow + slack + bond, "hostile bond: post-open clone != escrow + slack + bond");

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(address(hostileSeller), proceeds); // proceeds park
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT, address(hostileSeller), proceeds, fee);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(address(hostileSeller), bond); // bond parks
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.DisputeResolved(LOT, Resolution.ReleaseToSeller, address(hostileSeller));

        vm.prank(arbiter);
        a.resolveDispute(LOT, Resolution.ReleaseToSeller, bytes32(0));

        Lot memory lot = a.getLot(LOT);
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "hostile bond: phase != Settled");
        assertEq(uint256(lot.escrowAmount), 0, "hostile bond: escrow not zeroed (escrow still released)");
        assertEq(uint256(lot.disputeBond), 0, "hostile bond: bond not zeroed");

        // Hostile seller: proceeds + bond parked. Disjoint feeRecipient: paid in full, so only the fee
        // leaves the clone and the parked sum (proceeds + bond + slack) stays held.
        assertEq(a.pendingWithdrawal(address(hostileSeller)), proceeds + bond, "hostile bond: proceeds+bond not parked");
        assertEq(houseFeeRecipient.balance - feeRecvBefore, fee, "hostile bond: feeRecipient not paid");
        assertEq(address(a).balance, proceeds + bond + slack, "hostile bond: clone not holding parked proceeds + bond + slack");
        assertEq(cloneAfterOpen - address(a).balance, fee, "hostile bond: only the fee should have left the clone");

        // Toggle accept, claimPending pulls proceeds + bond together.
        hostileSeller.setReject(false);
        uint256 sellerEthBefore = address(hostileSeller).balance;
        uint256 cloneBeforeClaim = address(a).balance;

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalClaimed(address(hostileSeller), proceeds + bond);
        vm.prank(address(hostileSeller));
        a.claimPending();

        assertEq(a.pendingWithdrawal(address(hostileSeller)), 0, "hostile bond: pending not cleared");
        assertEq(address(hostileSeller).balance - sellerEthBefore, proceeds + bond, "hostile bond: not paid on claim");

        // claimPending drops the clone by exactly proceeds + bond, leaving only the bidder's slack.
        assertEq(cloneBeforeClaim - address(a).balance, proceeds + bond, "hostile bond: claim moved != parked proceeds + bond");
        assertEq(address(a).balance, slack, "hostile bond: post-claim clone residual != slack");
    }

    /// @dev ERC-20 cross-party no-strand on the same rail: ReleaseToSeller with opener == buyer, only the
    ///      SELLER denylisted. The seller's proceeds and bond both park while the disjoint feeRecipient is
    ///      paid in full as a real token transfer: one hostile payee and a healthy counterparty on the
    ///      same rail, not a globally-failing token.
    function test_HostileBondRecipientCrossParty_Token() public {
        H_DenylistERC20 dt = new H_DenylistERC20();
        dt.mint(bidder1, HOSTILE_TOKEN_MINT);
        dt.mint(seller, HOSTILE_TOKEN_MINT);

        SessionAuction a = _freshDeliveredLot(address(dt), TOKEN_DEPOSIT, TOKEN_BID);

        uint256 escrow = uint256(TOKEN_BID);
        uint256 fee = (escrow * FEE_BPS) / 10_000;
        uint256 proceeds = escrow - fee;
        uint256 bond = uint256(DISPUTE_BOND_AMT);
        uint256 slack = TOKEN_DEPOSIT - escrow; // bidder1 free, held by the clone throughout

        // Buyer opens (healthy, not denied) bonding the dispute; opener LOSES on ReleaseToSeller.
        _openDisputeAs(a, address(dt), bidder1, bond);

        // Physical-hold snapshot on the bond pool, ERC-20 rail: after the pull the clone holds escrow +
        // slack + bond. The denied seller leg parks both proceeds and bond; the disjoint fee leg transfers
        // for real.
        uint256 cloneAfterOpen = dt.balanceOf(address(a));
        assertEq(cloneAfterOpen, escrow + slack + bond, "cross-party: post-open clone != escrow + slack + bond");

        // Deny only the seller: its proceeds and bond park, the fee to feeRecipient pays.
        dt.setDenied(seller);
        uint256 feeRecvBefore = dt.balanceOf(houseFeeRecipient);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(seller, proceeds); // proceeds (denied) park
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT, seller, proceeds, fee);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(seller, bond); // bond (denied) parks
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.DisputeResolved(LOT, Resolution.ReleaseToSeller, seller);

        vm.prank(arbiter);
        a.resolveDispute(LOT, Resolution.ReleaseToSeller, bytes32(0));

        Lot memory lot = a.getLot(LOT);
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "cross-party: phase != Settled");
        assertEq(uint256(lot.escrowAmount), 0, "cross-party: escrow not zeroed");
        assertEq(uint256(lot.disputeBond), 0, "cross-party: bond not zeroed");

        // Hostile seller: proceeds + bond parked. Healthy feeRecipient: paid in full on the same rail, so
        // only the fee transfers out and the parked sum (proceeds + bond + slack) stays in the clone.
        assertEq(a.pendingWithdrawal(seller), proceeds + bond, "cross-party: seller proceeds+bond not parked");
        assertEq(dt.balanceOf(houseFeeRecipient) - feeRecvBefore, fee, "cross-party: feeRecipient not paid in full");
        assertEq(a.pendingWithdrawal(houseFeeRecipient), 0, "cross-party: fee wrongly parked");
        assertEq(dt.balanceOf(address(a)), proceeds + bond + slack, "cross-party: clone not holding parked proceeds + bond + slack");
        assertEq(cloneAfterOpen - dt.balanceOf(address(a)), fee, "cross-party: only the fee should have left the clone");

        // Un-deny, then claimPending pulls the seller's parked proceeds + bond as a real transfer.
        dt.setDenied(address(0));
        uint256 sellerBalBefore = dt.balanceOf(seller);
        uint256 cloneBeforeClaim = dt.balanceOf(address(a));

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalClaimed(seller, proceeds + bond);
        vm.prank(seller);
        a.claimPending();

        assertEq(a.pendingWithdrawal(seller), 0, "cross-party: seller pending not cleared");
        assertEq(dt.balanceOf(seller) - sellerBalBefore, proceeds + bond, "cross-party: seller not paid on claim");

        // claimPending drops the clone by exactly proceeds + bond, leaving only the bidder's slack.
        assertEq(cloneBeforeClaim - dt.balanceOf(address(a)), proceeds + bond, "cross-party: claim moved != parked proceeds + bond");
        assertEq(dt.balanceOf(address(a)), slack, "cross-party: post-claim clone residual != slack");
    }

    // Auto-release terminal with a hostile payee. releaseAfterWindow is its own release entrypoint that
    // emits DeliveryAutoReleased before the parked payout, exercising the no-strand fallback and the exact
    // ordering DeliveryAutoReleased -> WithdrawalCredited(seller) -> Released that the confirmReceipt /
    // reclaim / resolveDispute paths do not. Native + ERC-20.

    /// @dev Native: hostile SELLER (reverting receiver) on the permissionless timeout auto-release. The
    ///      gas-capped seller push fails so `proceeds` park, the feeRecipient is paid, the lot Settles.
    ///      Asserts event order DeliveryAutoReleased -> WithdrawalCredited -> Released, then claimPending.
    function test_HostileSeller_AutoRelease_Native() public {
        H_RejectingReceiver hostileSeller = new H_RejectingReceiver();
        SessionAuction a = _freshDeliveredLotWithSeller(address(0), NATIVE_DEPOSIT, NATIVE_BID, address(hostileSeller));

        uint256 escrow = uint256(NATIVE_BID);
        uint256 fee = (escrow * FEE_BPS) / 10_000;
        uint256 proceeds = escrow - fee;
        uint256 feeRecvBefore = houseFeeRecipient.balance;

        // Warp off the STORED deliveredAt so the boundary does not depend on call ordering.
        uint256 deliveredAt = uint256(a.getLot(LOT).deliveredAt);
        vm.warp(deliveredAt + DISPUTE_WINDOW_SEC);

        // Order: DeliveryAutoReleased, then the parked-proceeds credit, then the inner Released.
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.DeliveryAutoReleased(LOT, address(hostileSeller));
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(address(hostileSeller), proceeds);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT, address(hostileSeller), proceeds, fee);

        a.releaseAfterWindow(LOT); // permissionless

        Lot memory lot = a.getLot(LOT);
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "auto-release hostile: phase != Settled");
        assertEq(
            uint8(lot.deliveryState), uint8(DeliveryState.Released), "auto-release hostile: deliveryState != Released"
        );
        assertEq(uint256(lot.escrowAmount), 0, "auto-release hostile: escrow not zeroed");
        assertEq(a.pendingWithdrawal(address(hostileSeller)), proceeds, "auto-release hostile: proceeds not parked");
        assertEq(houseFeeRecipient.balance - feeRecvBefore, fee, "auto-release hostile: feeRecipient not paid");

        // Toggle accept, claimPending pulls the parked proceeds out to the seller.
        hostileSeller.setReject(false);
        uint256 sellerEthBefore = address(hostileSeller).balance;

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalClaimed(address(hostileSeller), proceeds);
        vm.prank(address(hostileSeller));
        a.claimPending();

        assertEq(a.pendingWithdrawal(address(hostileSeller)), 0, "auto-release hostile: pending not cleared");
        assertEq(address(hostileSeller).balance - sellerEthBefore, proceeds, "auto-release hostile: not paid on claim");
    }

    /// @dev ERC-20: the SELLER is denylisted (the push returns false) on the timeout auto-release, while
    ///      the disjoint feeRecipient is paid in full on the SAME rail. Same exact event ordering as the
    ///      native leg: DeliveryAutoReleased -> WithdrawalCredited(seller) -> Released, then claimPending.
    function test_HostileSeller_AutoRelease_Token() public {
        H_DenylistERC20 dt = new H_DenylistERC20();
        dt.mint(bidder1, HOSTILE_TOKEN_MINT);
        dt.mint(seller, HOSTILE_TOKEN_MINT);

        SessionAuction a = _freshDeliveredLot(address(dt), TOKEN_DEPOSIT, TOKEN_BID);

        uint256 escrow = uint256(TOKEN_BID);
        uint256 fee = (escrow * FEE_BPS) / 10_000;
        uint256 proceeds = escrow - fee;

        dt.setDenied(seller); // the seller proceeds push will return false and park
        uint256 feeRecvBefore = dt.balanceOf(houseFeeRecipient);

        uint256 deliveredAt = uint256(a.getLot(LOT).deliveredAt);
        vm.warp(deliveredAt + DISPUTE_WINDOW_SEC);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.DeliveryAutoReleased(LOT, seller);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(seller, proceeds);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT, seller, proceeds, fee);

        a.releaseAfterWindow(LOT);

        Lot memory lot = a.getLot(LOT);
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "auto-release token hostile: phase != Settled");
        assertEq(uint256(lot.escrowAmount), 0, "auto-release token hostile: escrow not zeroed");
        assertEq(a.pendingWithdrawal(seller), proceeds, "auto-release token hostile: proceeds not parked");
        // The disjoint feeRecipient is paid in full on the same rail (not parked).
        assertEq(
            dt.balanceOf(houseFeeRecipient) - feeRecvBefore, fee, "auto-release token hostile: feeRecipient not paid"
        );
        assertEq(a.pendingWithdrawal(houseFeeRecipient), 0, "auto-release token hostile: fee wrongly parked");

        dt.setDenied(address(0));
        uint256 sellerBalBefore = dt.balanceOf(seller);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalClaimed(seller, proceeds);
        vm.prank(seller);
        a.claimPending();

        assertEq(a.pendingWithdrawal(seller), 0, "auto-release token hostile: pending not cleared");
        assertEq(dt.balanceOf(seller) - sellerBalBefore, proceeds, "auto-release token hostile: not paid on claim");
    }

    // Hostile FEE RECIPIENT in isolation. A release pays the seller `proceeds` then the feeRecipient
    // `fee` as two separate pushes. This isolates the case the other hostile tests do not cover: the
    // second payout leg hostile while the first (seller) is healthy.
    // Native (reverting feeRecipient via initialize) + ERC-20 (denylist the feeRecipient).

    /// @dev Native: HEALTHY seller, HOSTILE feeRecipient (reverting receiver installed via initialize).
    ///      confirmReceipt pays the seller `proceeds` in full and parks only the `fee`; the lot Settles;
    ///      claimPending from the fee recipient then pulls the parked `fee`.
    function test_HostileFeeRecipient_Native() public {
        H_RejectingReceiver hostileFee = new H_RejectingReceiver();
        SessionAuction a = _freshDeliveredLotFeeRecipient(address(0), NATIVE_DEPOSIT, NATIVE_BID, address(hostileFee));

        uint256 escrow = uint256(NATIVE_BID);
        uint256 fee = (escrow * FEE_BPS) / 10_000;
        uint256 proceeds = escrow - fee;
        uint256 sellerBefore = seller.balance; // the HEALTHY default EOA seller

        // Seller paid in full; only the fee (the second payout leg) parks to the hostile recipient.
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(address(hostileFee), fee);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT, seller, proceeds, fee);

        vm.prank(bidder1);
        a.confirmReceipt(LOT, bytes32(0), "");

        Lot memory lot = a.getLot(LOT);
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "hostile fee native: phase != Settled");
        assertEq(uint256(lot.escrowAmount), 0, "hostile fee native: escrow not zeroed");
        assertEq(seller.balance - sellerBefore, proceeds, "hostile fee native: seller not paid in full");
        assertEq(a.pendingWithdrawal(address(hostileFee)), fee, "hostile fee native: fee not parked");
        assertEq(a.pendingWithdrawal(seller), 0, "hostile fee native: seller wrongly parked");

        // Toggle accept, the fee recipient claims its parked fee.
        hostileFee.setReject(false);
        uint256 feeEthBefore = address(hostileFee).balance;

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalClaimed(address(hostileFee), fee);
        vm.prank(address(hostileFee));
        a.claimPending();

        assertEq(a.pendingWithdrawal(address(hostileFee)), 0, "hostile fee native: pending not cleared");
        assertEq(address(hostileFee).balance - feeEthBefore, fee, "hostile fee native: not paid on claim");
    }

    /// @dev ERC-20: HEALTHY seller, HOSTILE feeRecipient via a per-recipient denylist on the SAME rail.
    ///      Only the fee push (the second payout leg) returns false and parks; the seller is paid in full
    ///      as a real token transfer; claimPending from the fee recipient pulls the parked fee.
    function test_HostileFeeRecipient_Token() public {
        H_DenylistERC20 dt = new H_DenylistERC20();
        dt.mint(bidder1, HOSTILE_TOKEN_MINT);
        dt.mint(seller, HOSTILE_TOKEN_MINT);

        SessionAuction a = _freshDeliveredLot(address(dt), TOKEN_DEPOSIT, TOKEN_BID);

        uint256 escrow = uint256(TOKEN_BID);
        uint256 fee = (escrow * FEE_BPS) / 10_000;
        uint256 proceeds = escrow - fee;

        dt.setDenied(houseFeeRecipient); // only the fee leg fails; the seller leg is healthy
        uint256 sellerBefore = dt.balanceOf(seller);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(houseFeeRecipient, fee);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT, seller, proceeds, fee);

        vm.prank(bidder1);
        a.confirmReceipt(LOT, bytes32(0), "");

        Lot memory lot = a.getLot(LOT);
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "hostile fee token: phase != Settled");
        assertEq(uint256(lot.escrowAmount), 0, "hostile fee token: escrow not zeroed");
        // Seller paid in full on the same rail; only the fee parks.
        assertEq(dt.balanceOf(seller) - sellerBefore, proceeds, "hostile fee token: seller not paid in full");
        assertEq(a.pendingWithdrawal(houseFeeRecipient), fee, "hostile fee token: fee not parked");
        assertEq(a.pendingWithdrawal(seller), 0, "hostile fee token: seller wrongly parked");

        dt.setDenied(address(0));
        uint256 feeBalBefore = dt.balanceOf(houseFeeRecipient);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalClaimed(houseFeeRecipient, fee);
        vm.prank(houseFeeRecipient);
        a.claimPending();

        assertEq(a.pendingWithdrawal(houseFeeRecipient), 0, "hostile fee token: pending not cleared");
        assertEq(dt.balanceOf(houseFeeRecipient) - feeBalBefore, fee, "hostile fee token: not paid on claim");
    }

    // Dust-to-seller rounding under cross-rail parity. fee = floor(amount*feeBps/10_000) and proceeds is
    // the remainder, so truncated-fee dust stays with the SELLER. Every other amount in this suite divides
    // feeBps exactly (token: 4e6*250/10000 == 100000), which hides a floor/ceil or scaling bug, so this
    // uses a non-divisible 6-dp token bid plus its scaled native equivalent.
    //
    // The cross-rail FEE is deliberately NOT asserted equal modulo decimals: with divisor 10_000/250 == 40
    // and 1e12 % 40 == 0, the native fee never truncates while the token fee floor(bid/40) truncates when
    // bid % 40 != 0, so the rails must diverge by the sub-6dp remainder the token rail drops. Instead
    // assert (a) per rail proceeds + fee == escrow with no wei lost, (b) per rail fee == floor with dust to
    // the seller, (c) escrow scales exactly, (d) the cross-rail fee gap nFee - tFee*1e12 ==
    // (bid % 40)*(1e12/40), the scaled dropped dust, pinning floor-rounding.
    function test_DenominationParityDustToSeller() public {
        // 4_000_001 * 250 / 10_000 == 100_000.025 -> truncates to 100_000, leaving 0.025 token-unit
        // dust that the seller keeps. The native bid is the exact 1e12 scale of the same value.
        uint128 tokenBid = 4_000_001; // 4_000_001 % 40 == 1, so the 6-dp fee truncates (real dust)
        uint128 nativeBid = uint128(uint256(tokenBid) * 1e12);
        uint256 scale = 1e12;

        (uint256 nProceeds, uint256 nFee, uint256 nEscrow) = _runDustPathAndMeasure(address(0), nativeBid);
        (uint256 tProceeds, uint256 tFee, uint256 tEscrow) = _runDustPathAndMeasure(address(token), tokenBid);

        // (a) No wei lost on EITHER rail: proceeds + fee is exactly the escrow (dust folded into proceeds).
        assertEq(nProceeds + nFee, nEscrow, "native: proceeds + fee != escrow (wei lost)");
        assertEq(tProceeds + tFee, tEscrow, "token: proceeds + fee != escrow (wei lost)");

        // (b) Each rail floors the fee (catches a ceil/round bug) and folds the dust into the SELLER's
        //     proceeds. The token rail must have a REAL remainder (else the rounding is untested).
        uint256 nFeeFloor = (uint256(nativeBid) * FEE_BPS) / 10_000;
        uint256 tFeeFloor = (uint256(tokenBid) * FEE_BPS) / 10_000;
        assertEq(nFee, nFeeFloor, "native fee != floor(amount*feeBps/10000)");
        assertEq(tFee, tFeeFloor, "token fee != floor(amount*feeBps/10000)");
        assertEq(nProceeds, uint256(nativeBid) - nFeeFloor, "native dust not retained by seller");
        assertEq(tProceeds, uint256(tokenBid) - tFeeFloor, "token dust not retained by seller");
        assertTrue((uint256(tokenBid) * FEE_BPS) % 10_000 != 0, "token bid unexpectedly divisible (no dust)");

        // (c) Escrow scales exactly across rails (the bid IS the 1e12 scale, no truncation on escrow).
        assertEq(nEscrow, tEscrow * scale, "dust: escrow not equal modulo decimals");

        // (d) The cross-rail fee gap is exactly the scaled dropped dust: native captures the sub-6dp
        //     remainder the token rail truncates. With divisor == 10_000/FEE_BPS == 40 and 1e12 % 40 == 0,
        //     the dropped token dust is (bid % divisor)*(scale/divisor). Pins floor-rounding on both rails.
        uint256 divisor = 10_000 / FEE_BPS; // 40 for FEE_BPS == 250 (a clean divisor of both 10_000 and 1e12)
        uint256 droppedTokenDustScaled = (uint256(tokenBid) % divisor) * (scale / divisor);
        assertEq(nFee - tFee * scale, droppedTokenDustScaled, "dust: cross-rail fee divergence != scaled dropped dust");
    }

    /// @dev Drive one rail to a confirmReceipt release with `bid` and return the EXPECTED + verified
    ///      (proceeds, fee, escrow). The reserve/deposit are scaled to the bid so the lot is valid on
    ///      both rails. Uses a deposit strictly above the bid so the lot opens above reserve.
    function _runDustPathAndMeasure(address paymentToken, uint128 bid)
        private
        returns (uint256 proceeds, uint256 fee, uint256 escrow)
    {
        uint256 deposit = uint256(bid) * 2; // ample free above the bid (slack reclaimable, not asserted here)
        uint96 reserve = uint96(uint256(bid) / 2); // strictly below the bid so reserve is met

        SessionAuction a = _initAuction(paymentToken);
        _openLot(a, paymentToken, reserve);
        _deposit(a, paymentToken, bidder1, deposit);
        _placeWinningBid(a, paymentToken, bidder1, bid);
        _hammer(a);
        _commitBidBook(a);
        _finalize(a, bid);
        _markDelivered(a);

        escrow = uint256(bid);
        fee = (escrow * FEE_BPS) / 10_000; // Math.mulDiv floor
        proceeds = escrow - fee; // dust (truncation remainder) folded into proceeds (to the seller)

        uint256 sellerBefore = _bal(paymentToken, seller);
        uint256 feeRecvBefore = _bal(paymentToken, houseFeeRecipient);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT, seller, proceeds, fee);

        vm.prank(bidder1);
        a.confirmReceipt(LOT, bytes32(0), "");

        // The release moved EXACTLY proceeds to the seller and fee to the recipient (no wei lost).
        assertEq(_bal(paymentToken, seller) - sellerBefore, proceeds, "dust: seller payout != proceeds");
        assertEq(_bal(paymentToken, houseFeeRecipient) - feeRecvBefore, fee, "dust: feeRecipient payout != fee");
        assertEq(uint256(a.getLot(LOT).escrowAmount), 0, "dust: escrow not zeroed");
    }

    // Cross-rail parity of the bond pull: openDispute is the only settlement entry that pulls value, and
    // each rail must reject the other rail's call shape with WrongBond and pull nothing.

    /// @dev Native clone: openDispute with msg.value != bond (under AND over) reverts WrongBond and
    ///      pulls nothing (disputeBond stays 0, deliveryState stays Delivered, no DisputeOpened, clone
    ///      balance unchanged).
    function test_OpenDisputePullParity_NativeWrongBond() public {
        SessionAuction a = _freshDeliveredLot(address(0), NATIVE_DEPOSIT, NATIVE_BID);
        uint256 bond = uint256(DISPUTE_BOND_AMT);
        uint256 cloneBefore = address(a).balance;

        // Under-bond: the native _pull assert (msg.value == _disputeBondAmt) surfaces WrongBond.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongBond.selector);
        a.openDispute{value: bond - 1}(LOT, keccak256("claim"));

        // Over-bond: same revert; an over-payment must not be silently kept either.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongBond.selector);
        a.openDispute{value: bond + 1}(LOT, keccak256("claim"));

        Lot memory lot = a.getLot(LOT);
        assertEq(uint256(lot.disputeBond), 0, "native wrong-bond: bond pulled despite revert");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Delivered), "native wrong-bond: state moved");
        assertEq(address(a).balance, cloneBefore, "native wrong-bond: clone balance changed");
    }

    /// @dev ERC-20 clone: openDispute carrying a nonzero msg.value (the native shape) reverts
    ///      WrongBond and pulls nothing, even with the token bond approved. The ERC-20 _pull asserts
    ///      msg.value == 0.
    function test_OpenDisputePullParity_TokenNonzeroValue() public {
        SessionAuction a = _freshDeliveredLot(address(token), TOKEN_DEPOSIT, TOKEN_BID);
        uint256 bond = uint256(DISPUTE_BOND_AMT);
        uint256 cloneTokenBefore = token.balanceOf(address(a));

        vm.prank(bidder1);
        token.approve(address(a), bond); // approve so only the msg.value==0 assert can fail

        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongBond.selector);
        a.openDispute{value: 1}(LOT, keccak256("claim")); // nonzero msg.value on the ERC-20 rail

        Lot memory lot = a.getLot(LOT);
        assertEq(uint256(lot.disputeBond), 0, "token wrong-bond: bond pulled despite revert");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Delivered), "token wrong-bond: state moved");
        assertEq(token.balanceOf(address(a)), cloneTokenBefore, "token wrong-bond: clone token balance changed");
    }

    /// @dev ERC-20 clone, the other token-pull failure shape: msg.value == 0 (correct ERC-20 shape) but
    ///      the bidder has NOT approved the bond, so the bond safeTransferFrom bubbles the standard ERC20
    ///      ERC20InsufficientAllowance. The bond pulls nothing: disputeBond stays 0, state stays
    ///      Delivered, the clone token balance is unchanged.
    function test_OpenDisputePull_TokenInsufficientAllowance() public {
        SessionAuction a = _freshDeliveredLot(address(token), TOKEN_DEPOSIT, TOKEN_BID);
        uint256 cloneTokenBefore = token.balanceOf(address(a));
        uint256 bidderTokenBefore = token.balanceOf(bidder1);

        // No approval (allowance == 0 < the bond): the bond safeTransferFrom reverts, allowance checked
        // first so ERC20InsufficientAllowance is surfaced.
        assertEq(token.allowance(bidder1, address(a)), 0, "precondition: bidder unexpectedly approved");

        // Match the FULL error data (selector + params), not the bare selector: bare-selector
        // vm.expectRevert does not match a revert carrying parameter data on this foundry/OZ pair. Spender
        // is the clone `a` (it does transferFrom FROM bidder1), allowance 0, needed the flat DISPUTE_BOND_AMT.
        vm.prank(bidder1);
        vm.expectRevert(
            abi.encodeWithSelector(
                IERC20Errors.ERC20InsufficientAllowance.selector, address(a), uint256(0), uint256(DISPUTE_BOND_AMT)
            )
        );
        a.openDispute(LOT, keccak256("claim")); // msg.value == 0 (correct ERC-20 shape), no allowance

        Lot memory lot = a.getLot(LOT);
        assertEq(uint256(lot.disputeBond), 0, "token no-allowance: bond pulled despite revert");
        assertEq(lot.disputeOpener, address(0), "token no-allowance: opener set despite revert");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Delivered), "token no-allowance: state moved");
        assertEq(token.balanceOf(address(a)), cloneTokenBefore, "token no-allowance: clone token balance changed");
        assertEq(token.balanceOf(bidder1), bidderTokenBefore, "token no-allowance: bidder token balance changed");
    }

    // IN-leg parity of the bond pull: the successful openDispute bond is the only value-IN path,
    // symmetric to the value-OUT parity. A clone-balance delta alone cannot prove the bond came FROM the
    // opener (a mis-attributed msg.value or a pull from the wrong account would still satisfy it), so
    // these tests pin the opener-side debit directly.

    /// @dev Cross-rail IN-leg parity: a successful openDispute debits the opener by exactly the flat
    ///      DISPUTE_BOND_AMT on both rails (native msg.value, ERC-20 safeTransferFrom), not scaled by
    ///      1e12. Also pins, per rail, that openDispute is value-IN only: escrow untouched and frozen, no
    ///      payout during open, the clone rises by exactly the bond, slack stays held as the bidder's
    ///      free. Opener is the BUYER on both rails.
    function test_OpenDisputeInLegParity_BuyerOpener() public {
        // Native rail.
        SessionAuction an = _freshDeliveredLot(address(0), NATIVE_DEPOSIT, NATIVE_BID);
        uint256 bond = uint256(DISPUTE_BOND_AMT);
        uint256 escrowN = uint256(NATIVE_BID);
        uint256 slackN = NATIVE_DEPOSIT - escrowN;

        uint256 cloneBeforeN = address(an).balance;
        assertEq(cloneBeforeN, escrowN + slackN, "in-leg native: pre-open clone != escrow + slack");
        uint256 escrowHeldBeforeN = uint256(an.getLot(LOT).escrowAmount);

        (uint256 cloneAfterN, uint256 openerOutN) = _openDisputeAs(an, address(0), bidder1, bond);

        // Value-IN ONLY: opener debited exactly the bond; clone rises by exactly the bond; escrow frozen.
        assertEq(openerOutN, bond, "in-leg native: opener (buyer) not debited exactly the bond");
        assertEq(cloneAfterN - cloneBeforeN, bond, "in-leg native: clone did not rise by exactly the bond");

        Lot memory ln = an.getLot(LOT);
        assertEq(uint8(ln.deliveryState), uint8(DeliveryState.Disputed), "in-leg native: not Disputed");
        assertEq(uint256(ln.escrowAmount), escrowHeldBeforeN, "in-leg native: escrow moved on open (not value-IN only)");
        assertEq(uint256(ln.escrowAmount), escrowN, "in-leg native: escrow no longer held in full");
        assertEq(uint256(ln.disputeBond), bond, "in-leg native: stored bond != pulled bond");

        // The bond is a separate pool, so the disjoint slack is untouched by the pull.
        assertEq(an.withdrawableFree(LOT, bidder1), slackN, "in-leg native: slack pool perturbed by bond pull");

        // ERC-20 rail (bidder funded above the flat bond; default token holds only INITIAL_TOKEN).
        SessionAuction at = _freshDeliveredLot(address(token), TOKEN_DEPOSIT, TOKEN_BID);
        token.mint(bidder1, DISPUTE_BOND_AMT); // cover the flat 1e17 bond on the 6-dp rail
        uint256 escrowT = uint256(TOKEN_BID);
        uint256 slackT = TOKEN_DEPOSIT - escrowT;

        uint256 cloneBeforeT = token.balanceOf(address(at));
        assertEq(cloneBeforeT, escrowT + slackT, "in-leg token: pre-open clone != escrow + slack");
        uint256 escrowHeldBeforeT = uint256(at.getLot(LOT).escrowAmount);

        (uint256 cloneAfterT, uint256 openerOutT) = _openDisputeAs(at, address(token), bidder1, bond);

        assertEq(openerOutT, bond, "in-leg token: opener (buyer) not debited exactly the bond");
        assertEq(cloneAfterT - cloneBeforeT, bond, "in-leg token: clone did not rise by exactly the bond");

        Lot memory lt = at.getLot(LOT);
        assertEq(uint8(lt.deliveryState), uint8(DeliveryState.Disputed), "in-leg token: not Disputed");
        assertEq(uint256(lt.escrowAmount), escrowHeldBeforeT, "in-leg token: escrow moved on open (not value-IN only)");
        assertEq(uint256(lt.escrowAmount), escrowT, "in-leg token: escrow no longer held in full");
        assertEq(uint256(lt.disputeBond), bond, "in-leg token: stored bond != pulled bond");
        assertEq(at.withdrawableFree(LOT, bidder1), slackT, "in-leg token: slack pool perturbed by bond pull");

        // Cross-rail IN-leg parity: the bond debit is the same flat amount on both rails, not scaled by
        // 1e12 (asserting openerOutN == openerOutT*1e12 would be 1e17 == 1e29, rejecting a correct pull).
        assertEq(openerOutN, openerOutT, "in-leg: bond debit not equal cross-rail (flat, not scaled)");
        assertEq(openerOutN, bond, "in-leg: native bond debit != flat DISPUTE_BOND_AMT");
        assertEq(openerOutT, bond, "in-leg: token bond debit != flat DISPUTE_BOND_AMT");
    }

    /// @dev IN-leg SOURCE: on a successful openDispute the bond is sourced from the OPENER (msg.sender),
    ///      not the counterparty. With the SELLER opening, the seller drops by exactly the bond and the
    ///      BUYER is unchanged (buyer-opener is covered by the parity test). Triangulates the source on
    ///      both rails: clone +bond, opener -bond, counterparty 0.
    function test_OpenDisputeInLegSource_SellerOpener_CounterpartyUntouched() public {
        // Native rail: SELLER opens, BUYER (bidder1) must be untouched.
        SessionAuction an = _freshDeliveredLot(address(0), NATIVE_DEPOSIT, NATIVE_BID);
        uint256 bond = uint256(DISPUTE_BOND_AMT);

        uint256 sellerBeforeN = seller.balance; // the opener
        uint256 buyerBeforeN = bidder1.balance; // the counterparty (must NOT fund the bond)
        uint256 cloneBeforeN = address(an).balance;

        (uint256 cloneAfterN, uint256 openerOutN) = _openDisputeAs(an, address(0), seller, bond);

        // Opener (seller) debited exactly the bond; clone rose by exactly the bond.
        assertEq(openerOutN, bond, "in-leg src native: seller (opener) not debited exactly the bond");
        assertEq(sellerBeforeN - seller.balance, bond, "in-leg src native: seller debit != bond");
        assertEq(cloneAfterN - cloneBeforeN, bond, "in-leg src native: clone rise != bond");

        // Counterparty (buyer) untouched: the bond was not mis-sourced from the non-opener.
        assertEq(bidder1.balance, buyerBeforeN, "in-leg src native: buyer (counterparty) wrongly funded the bond");

        // ERC-20 rail: SELLER opens, BUYER (bidder1) must be untouched.
        SessionAuction at = _freshDeliveredLot(address(token), TOKEN_DEPOSIT, TOKEN_BID);
        token.mint(seller, DISPUTE_BOND_AMT); // opener funds the flat 1e17 bond on the 6-dp rail

        uint256 sellerBeforeT = token.balanceOf(seller); // opener
        uint256 buyerBeforeT = token.balanceOf(bidder1); // counterparty
        uint256 cloneBeforeT = token.balanceOf(address(at));

        (uint256 cloneAfterT, uint256 openerOutT) = _openDisputeAs(at, address(token), seller, bond);

        assertEq(openerOutT, bond, "in-leg src token: seller (opener) not debited exactly the bond");
        assertEq(sellerBeforeT - token.balanceOf(seller), bond, "in-leg src token: seller debit != bond");
        assertEq(cloneAfterT - cloneBeforeT, bond, "in-leg src token: clone rise != bond");

        // Counterparty (buyer) token balance UNTOUCHED: safeTransferFrom must use the opener as `from`.
        assertEq(token.balanceOf(bidder1), buyerBeforeT, "in-leg src token: buyer (counterparty) wrongly funded the bond");

        // The seller-opener debit equals the buyer-opener debit cross-rail too (flat bond, opener-agnostic).
        assertEq(openerOutN, openerOutT, "in-leg src: seller-opener debit not equal cross-rail (flat)");
        assertEq(openerOutN, bond, "in-leg src: native seller-opener debit != flat DISPUTE_BOND_AMT");
    }

    // Pre-state drivers (real entrypoints).

    /// @dev Deploy a fresh clone and initialize it for `paymentToken` (the only per-rail field).
    function _initAuction(address paymentToken) private returns (SessionAuction a) {
        a = SessionAuction(Clones.clone(address(impl)));
        InitConfig memory cfg = _defaultInitConfig(paymentToken);
        a.initialize(cfg);
    }

    /// @dev Deploy a fresh clone for `paymentToken` with the fee sink overridden to `feeRecipient` (to
    ///      install a hostile native fee recipient while the seller stays the healthy default EOA). Only
    ///      that one config field differs.
    function _initAuctionFee(address paymentToken, address feeRecipient) private returns (SessionAuction a) {
        a = SessionAuction(Clones.clone(address(impl)));
        InitConfig memory cfg = _defaultInitConfig(paymentToken);
        cfg.feeRecipient = feeRecipient;
        a.initialize(cfg);
    }

    /// @dev Same as _freshDeliveredLot but with the clone's fee sink set to `feeRecipient` (the default
    ///      healthy seller still marks delivered), isolating a failing fee leg from a healthy seller leg.
    function _freshDeliveredLotFeeRecipient(address paymentToken, uint256 deposit, uint128 bid, address feeRecipient)
        private
        returns (SessionAuction a)
    {
        a = _initAuctionFee(paymentToken, feeRecipient);
        _openLot(a, paymentToken, uint96(_reserveFor(paymentToken)));
        _deposit(a, paymentToken, bidder1, deposit);
        _placeWinningBid(a, paymentToken, bidder1, bid);
        _hammer(a);
        _commitBidBook(a);
        _finalize(a, bid);
        _markDelivered(a);
    }

    function _openLot(
        SessionAuction a,
        address,
        /*paymentToken*/
        uint96 reserve
    )
        private
    {
        // Read the clock via _now() (cheatcode), not the bare TIMESTAMP opcode: under via_ir an inlined
        // block.timestamp folds to the first rail's value and stamps a stale endsAt on the second. See _now().
        vm.prank(address(hammer));
        a.openLot(LOT, seller, reserve, uint64(_now() + 1 days));
    }

    /// @dev Open a lot whose seller is an explicit address (used to install a hostile native seller).
    function _openLotWithSeller(SessionAuction a, uint96 reserve, address theSeller) private {
        vm.prank(address(hammer));
        a.openLot(LOT, theSeller, reserve, uint64(_now() + 1 days));
    }

    /// @dev depositCeiling for `principal`. Native sends msg.value == amount; ERC-20 approves the clone
    ///      and sends msg.value == 0 (the pull-vs-send rail split).
    function _deposit(SessionAuction a, address paymentToken, address principal, uint256 amount) private {
        if (paymentToken == address(0)) {
            vm.prank(principal);
            a.depositCeiling{value: amount}(LOT, amount);
        } else {
            vm.prank(principal);
            MockERC20(paymentToken).approve(address(a), amount);
            vm.prank(principal);
            a.depositCeiling(LOT, amount);
        }
    }

    /// @dev Place one strictly-above-reserve winning bid for `principal`, with a real EIP-712 ceiling
    ///      signature and a structurally correct attestation quote (observedPrevTop == highBid == 0 on
    ///      the first bid). The operatorKeyId is the keyId seeded in _defaultInitConfig.
    function _placeWinningBid(
        SessionAuction a,
        address,
        /*paymentToken*/
        address principal,
        uint128 amount
    )
        private
    {
        uint192 nonceKey = _nonceKeyFor(SESSION_ID, LOT, principal);
        bytes32 ceilingCommit = keccak256(abi.encode(uint128(amount), bytes32("salt"))); // maxBid == amount

        // Read the clock via _now() (cheatcode), not the bare TIMESTAMP opcode: under via_ir an inlined
        // block.timestamp in this struct literal folds to the first rail's value and stamps a stale
        // deadline on the second (placeBid reverts EnvelopeExpired). See _now().
        uint256 nowTs = _now();

        Ceiling memory c = Ceiling({
            principal: principal,
            sessionId: SESSION_ID,
            lotId: LOT,
            ceilingCommit: ceilingCommit,
            strategy: 0,
            deadline: uint64(nowTs + 1 hours),
            maxBids: uint64(MAX_EXTENSIONS) + 8,
            nonceKey: nonceKey
        });

        bytes memory sig = _signCeiling(address(a), c, bidder1Key);

        bytes32 quoteNonce = keccak256(abi.encode(principal, amount, "quote-nonce"));
        AttestationQuote memory quote = _realQuote(c, LOT, amount, 0, 0, quoteNonce);

        bytes32 keyId = _baseOperatorKeyId();

        // KYC gate: placeBid reverts Unauthorized() when paddleOf(principal) == 0, and the PaddleRegistry
        // stub returns 0, so mock a distinct nonzero paddle for `principal`. The exact value is irrelevant
        // to these tests (no payout path reads it), only that it is != 0.
        _mockPaddle(principal, _paddleFor(principal));

        // Any caller may submit; the principal is bound by the ceiling signature, not by msg.sender.
        vm.prank(principal);
        a.placeBid(
            c,
            LOT,
            principal,
            0,
            /* bidIndex */
            amount,
            sig,
            keyId,
            quote
        );
    }

    function _hammer(SessionAuction a) private {
        vm.warp(block.timestamp + 2 days); // past endsAt
        a.hammer(LOT);
    }

    function _commitBidBook(SessionAuction a) private {
        vm.prank(settler);
        a.commitBidBook(LOT, keccak256("bidbook-root"));
    }

    /// @dev Reveal the winning bid (maxBid == the public bid on this rail, salt == "salt", matching
    ///      the commit built in _placeWinningBid) so the reveal gate is satisfied, close the AC
    ///      window, then finalize Hammered -> Awaiting.
    function _finalize(SessionAuction a, uint128 maxBid) private {
        uint64 wseq = a.getLot(LOT).winnerSeq;
        vm.prank(bidder1);
        a.reveal(LOT, wseq, maxBid, bytes32("salt"));
        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1); // AC window closed
        a.finalizeWinner(LOT);
    }

    function _markDelivered(SessionAuction a) private {
        vm.prank(seller);
        a.markDelivered(LOT, keccak256("delivery-proof"), "ipfs://delivery");
    }

    /// @dev Build a lot in DeliveryState.Delivered for `paymentToken` with a measured bid.
    function _freshDeliveredLot(address paymentToken, uint256 deposit, uint128 bid) private returns (SessionAuction a) {
        a = _initAuction(paymentToken);
        _openLot(a, paymentToken, uint96(_reserveFor(paymentToken)));
        _deposit(a, paymentToken, bidder1, deposit);
        _placeWinningBid(a, paymentToken, bidder1, bid);
        _hammer(a);
        _commitBidBook(a);
        _finalize(a, bid);
        _markDelivered(a);
    }

    /// @dev Same as _freshDeliveredLot but with an explicit seller address (hostile native seller).
    function _freshDeliveredLotWithSeller(address paymentToken, uint256 deposit, uint128 bid, address theSeller)
        private
        returns (SessionAuction a)
    {
        a = _initAuction(paymentToken);
        _openLotWithSeller(a, uint96(_reserveFor(paymentToken)), theSeller);
        _deposit(a, paymentToken, bidder1, deposit);
        _placeWinningBid(a, paymentToken, bidder1, bid);
        _hammer(a);
        _commitBidBook(a);
        _finalize(a, bid);
        // a hostile seller still calls markDelivered (emits/stores only, no value transfer)
        vm.prank(theSeller);
        a.markDelivered(LOT, keccak256("delivery-proof"), "ipfs://delivery");
    }

    /// @dev Build a lot in DeliveryState.AwaitingDelivery (finalized, seller has NOT delivered).
    function _freshAwaitingLot(address paymentToken, uint256 deposit, uint128 bid) private returns (SessionAuction a) {
        a = _initAuction(paymentToken);
        _openLot(a, paymentToken, uint96(_reserveFor(paymentToken)));
        _deposit(a, paymentToken, bidder1, deposit);
        _placeWinningBid(a, paymentToken, bidder1, bid);
        _hammer(a);
        _commitBidBook(a);
        _finalize(a, bid);
    }

    /// @dev Reveal as an explicit buyer (used when the buyer is a contract/ERC-1271 principal whose
    ///      address differs from bidder1). reveal checks msg.sender == _bidOf principal.
    function _finalizeAs(SessionAuction a, address theBuyer, uint128 maxBid) private {
        uint64 wseq = a.getLot(LOT).winnerSeq;
        vm.prank(theBuyer);
        a.reveal(LOT, wseq, maxBid, bytes32("salt"));
        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1); // AC window closed
        a.finalizeWinner(LOT);
    }

    /// @dev Build an AwaitingDelivery lot whose BUYER (principal/highBidder) is `theBuyer` (a contract
    ///      for the native hostile-refund cases). The seller is the default healthy EOA. `theBuyer`
    ///      must be ERC-1271-permissive (the ceiling sig is checked via SignatureChecker), and is
    ///      funded here for the native deposit.
    function _freshAwaitingLotWithBuyer(address paymentToken, uint256 deposit, uint128 bid, address theBuyer)
        private
        returns (SessionAuction a)
    {
        a = _initAuction(paymentToken);
        if (paymentToken == address(0)) vm.deal(theBuyer, INITIAL_ETH);
        _openLot(a, paymentToken, uint96(_reserveFor(paymentToken)));
        _deposit(a, paymentToken, theBuyer, deposit);
        _placeWinningBid(a, paymentToken, theBuyer, bid);
        _hammer(a);
        _commitBidBook(a);
        _finalizeAs(a, theBuyer, bid);
    }

    /// @dev Same as above but driven through to DeliveryState.Delivered (the default seller marks it),
    ///      so the lot is ready for openDispute + resolveDispute(RefundToBuyer) against a hostile buyer.
    function _freshDeliveredLotWithBuyer(address paymentToken, uint256 deposit, uint128 bid, address theBuyer)
        private
        returns (SessionAuction a)
    {
        a = _freshAwaitingLotWithBuyer(paymentToken, deposit, bid, theBuyer);
        _markDelivered(a); // default seller marks delivered (no value transfer)
    }

    /// @dev openDispute as `opener`, bonding the bond. Native sends msg.value == bond; ERC-20 approves
    ///      then sends msg.value == 0 (the pull-vs-send rail split). Returns the clone-after balance and
    ///      the measured `openerOut` debit, and asserts the opener-side debit (openerBefore - openerAfter
    ///      == bond), which a clone-balance delta alone cannot prove (a mis-sourced pull would still
    ///      satisfy it). openDispute only pulls value in (no payout fires), so the opener has no offsetting
    ///      credit. Native: foundry gasprice == 0, so the balance drops by exactly msg.value. ERC-20:
    ///      approve moves allowance only, so the only balance change is the safeTransferFrom of `bond`.
    function _openDisputeAs(SessionAuction a, address paymentToken, address opener, uint256 bond)
        private
        returns (uint256 cloneBalAfter, uint256 openerOut)
    {
        uint256 openerBefore = _bal(paymentToken, opener);

        if (paymentToken == address(0)) {
            // expectEmit binds to the next call (openDispute), so set it immediately before.
            vm.expectEmit(true, true, true, true, address(a));
            emit ISessionAuction.DisputeOpened(LOT, opener, bond, keccak256("claim"));
            vm.prank(opener);
            a.openDispute{value: bond}(LOT, keccak256("claim"));
        } else {
            // Approve first, then bind expectEmit to openDispute. Approve moves allowance only, so
            // openerBefore (captured above) is still the pre-pull balance.
            vm.prank(opener);
            MockERC20(paymentToken).approve(address(a), bond);
            vm.expectEmit(true, true, true, true, address(a));
            emit ISessionAuction.DisputeOpened(LOT, opener, bond, keccak256("claim"));
            vm.prank(opener);
            a.openDispute(LOT, keccak256("claim")); // msg.value == 0 for ERC-20
        }

        cloneBalAfter = _bal(paymentToken, address(a));

        // IN-leg parity: the bond debit pinned on the OPENER, identically on both rails.
        openerOut = openerBefore - _bal(paymentToken, opener);
        assertEq(openerOut, bond, "openDispute: opener not debited exactly the bond (IN-leg parity)");
    }

    // Pure helpers: balances, nonceKey, EIP-712 ceiling digest + signature.

    /// @dev Mock PaddleRegistry.paddleOf(principal) -> a nonzero KYC paddle. The stub returns 0
    ///      unconditionally, and placeBid reverts Unauthorized() when the paddle is 0, so every accepted
    ///      bid needs this mock to clear the KYC gate.
    function _mockPaddle(address principal, uint16 paddleId) private {
        vm.mockCall(
            address(paddles),
            abi.encodeWithSelector(IPaddleRegistry.paddleOf.selector, principal),
            abi.encode(paddleId)
        );
    }

    /// @dev A stable distinct nonzero paddle for `principal`: the low 15 address bits OR 0x8000, always
    ///      in [0x8000, 0xFFFF] so it never collapses to 0 (the unregistered sentinel).
    function _paddleFor(address principal) private pure returns (uint16) {
        return uint16(uint256(uint160(principal)) & 0x7FFF) | 0x8000;
    }

    function _reserveFor(address paymentToken) private pure returns (uint256) {
        return paymentToken == address(0) ? NATIVE_RESERVE : TOKEN_RESERVE;
    }

    /// @dev Rail-agnostic balance: native uses address.balance, ERC-20 uses token.balanceOf.
    function _bal(address paymentToken, address who) private view returns (uint256) {
        return paymentToken == address(0) ? who.balance : MockERC20(paymentToken).balanceOf(who);
    }

    /// @dev Live block timestamp via the cheatcode, not the bare TIMESTAMP opcode. Under via_ir an
    ///      inlined `block.timestamp + delta` in a struct/argument literal is constant-folded to its
    ///      first-call value and reused on the second rail (which has warped forward), stamping a stale
    ///      endsAt/deadline that reverts AuctionEnded / EnvelopeExpired. The cheatcode result is not
    ///      foldable, so each rail reads its own clock.
    function _now() private view returns (uint256) {
        return vm.getBlockTimestamp();
    }

    /// @dev nonceKey == uint192(uint256(keccak256(abi.encode(sessionId, lotId, principal)))), matching
    ///      the contract's per-(session, lot, principal) nonce key derivation.
    function _nonceKeyFor(bytes32 sessionId, uint256 lotId, address principal) private pure returns (uint192) {
        return uint192(uint256(keccak256(abi.encode(sessionId, lotId, principal))));
    }

    /// @dev EIP-712 domain separator for the clone (EIP712("Hammer","1")).
    function _domainSeparator(address clone) private view returns (bytes32) {
        return keccak256(abi.encode(EIP712_TYPE_HASH, HASHED_NAME, HASHED_VERSION, block.chainid, clone));
    }

    /// @dev Sign the Ceiling struct over the clone EIP-712 domain with `key` (matches the contract's
    ///      ceiling struct hash so placeBid accepts the signature).
    function _signCeiling(address clone, Ceiling memory c, uint256 key) private view returns (bytes memory) {
        bytes32 structHash = keccak256(
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
        bytes32 digest = keccak256(abi.encodePacked("\x19\x01", _domainSeparator(clone), structHash));
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(key, digest);
        return abi.encodePacked(r, s, v);
    }
}
