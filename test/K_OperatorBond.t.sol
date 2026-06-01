// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// AgentBond economic remedy and fund conservation.
// Covers deposit -> recordClaim -> settleSlash -> claimSlash (victims paid pro-rata by recorded harm),
// remainder to Treasury, slashed stake unrecoverable, and a clean session fully reclaimable.
// recordClaim is driven through a registered, initialized SessionAuction clone (not a mock) so it
// exercises the real onlyAuction + session-binding gate: the caller's sessionId() must match the claim.

import {HammerBase}      from "./HammerBase.t.sol";
import {AgentBond}       from "../src/AgentBond.sol";
import {SessionAuction} from "../src/SessionAuction.sol";
import {ISessionAuction} from "../src/interfaces/ISessionAuction.sol";
import {InitConfig}      from "../src/types/HammerTypes.sol";
import {Clones}          from "@openzeppelin/contracts/proxy/Clones.sol";
import {ERC20}           from "@openzeppelin/contracts/token/ERC20/ERC20.sol";

contract OperatorBondTest is HammerBase {
    bytes32 private sid;

    function setUp() public override {
        super.setUp();

        // Initialize the canonical `auction` clone (registered in HammerBase) so its sessionId() equals
        // the session recordClaim is bound to; this clone is the onlyAuction caller below.
        vm.prank(address(hammer));
        auction.initialize(_defaultInitConfig(address(0)));

        sid = SESSION_ID;
    }

    /// Warp strictly past the clone's bondClaimsCloseAt (the latest any claim can land), then close the
    /// session through the clone that owns it. Close is permissionless once past the deadline.
    function _closeAfterDeadline(bytes32 s, SessionAuction clone) private {
        vm.warp(clone.bondClaimsCloseAt() + 1); // strictly past the deadline (> not >=)
        operatorBond.closeSession(s, address(clone));
    }

    /// K-01: a slash distributes the WHOLE pool: victims pro-rata by recorded harm, remainder to Treasury,
    ///       slashed stake unrecoverable, and the native bond pool conserves to the wei (10 in == 4 + 6 out).
    function test_SlashDistributesProRataAndConserves() public {
        vm.deal(operator1, 6 ether);
        vm.prank(operator1);
        operatorBond.deposit{value: 6 ether}(sid, address(auction), 6 ether);

        vm.deal(operator2, 4 ether);
        vm.prank(operator2);
        operatorBond.deposit{value: 4 ether}(sid, address(auction), 4 ether);

        assertEq(operatorBond.bondOf(sid), 10 ether, "K-01: pool = sum of stakes");

        // Record two victims through the real onlyAuction + session-binding gate (caller is the
        // registered auction). totalClaims = 4; pool = 10; so toVictims = min(10,4) = 4, toTreasury = 6.
        vm.prank(address(auction));
        operatorBond.recordClaim(sid, bidder1, 3 ether);
        vm.prank(address(auction));
        operatorBond.recordClaim(sid, bidder2, 1 ether);

        _closeAfterDeadline(sid, auction);

        uint256 treasuryBefore = address(treasury).balance;
        operatorBond.settleSlash(sid); // permissionless once the session is closed
        assertEq(address(treasury).balance - treasuryBefore, 6 ether, "K-01: remainder to Treasury");

        uint256 v1 = bidder1.balance;
        vm.prank(bidder1);
        operatorBond.claimSlash(sid);
        assertEq(bidder1.balance - v1, 3 ether, "K-01: victim1 pro-rata (4 * 3/4)");

        uint256 v2 = bidder2.balance;
        vm.prank(bidder2);
        operatorBond.claimSlash(sid);
        assertEq(bidder2.balance - v2, 1 ether, "K-01: victim2 pro-rata (4 * 1/4)");

        // Slashed operators recover nothing: the whole pool was distributed.
        vm.prank(operator1);
        vm.expectRevert(AgentBond.NothingToWithdraw.selector);
        operatorBond.withdraw(sid);

        assertEq(address(operatorBond).balance, 0, "K-01: bond pool fully distributed (conserved)");
    }

    /// K-02: a clean (no-claim) session lets each operator reclaim its full stake.
    function test_CleanSessionWithdrawReturnsFullStake() public {
        vm.deal(operator1, 5 ether);
        vm.prank(operator1);
        operatorBond.deposit{value: 5 ether}(sid, address(auction), 5 ether);

        _closeAfterDeadline(sid, auction); // clean withdraw is still gated on session close

        uint256 before = operator1.balance;
        vm.prank(operator1);
        operatorBond.withdraw(sid);
        assertEq(operator1.balance - before, 5 ether, "K-02: clean withdraw returns the full stake");
        assertEq(operatorBond.bondOf(sid), 0, "K-02: pool drained on withdraw");
    }

    /// K-03: an open (recorded-but-unsettled) claim gates withdraw with WindowOpen.
    function test_RevertWhen_WithdrawWhileClaimUnsettled() public {
        vm.deal(operator1, 5 ether);
        vm.prank(operator1);
        operatorBond.deposit{value: 5 ether}(sid, address(auction), 5 ether);

        vm.prank(address(auction));
        operatorBond.recordClaim(sid, bidder1, 1 ether);

        _closeAfterDeadline(sid, auction); // pass the close gate so the claim-unsettled gate is what surfaces

        vm.prank(operator1);
        vm.expectRevert(AgentBond.WindowOpen.selector);
        operatorBond.withdraw(sid);
    }

    /// K-04: a registered clone cannot inflate a DIFFERENT session's claim ledger; recordClaim is bound to
    ///       the caller clone's own sessionId().
    function test_RevertWhen_RecordClaimCrossSession() public {
        vm.prank(address(auction));
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        operatorBond.recordClaim(keccak256("OTHER_SESSION"), bidder1, 1 ether);
    }

    /// K-05: an unregistered EOA cannot record a claim (onlyAuction).
    function test_RevertWhen_RecordClaimUnregistered() public {
        vm.prank(bidder3);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        operatorBond.recordClaim(sid, bidder1, 1 ether);
    }

    /// K-06: a non-liveness slash with no victim claims routes the whole pool to Treasury.
    function test_NonLivenessSlashRoutesWholePoolToTreasury() public {
        vm.deal(operator1, 3 ether);
        vm.prank(operator1);
        operatorBond.deposit{value: 3 ether}(sid, address(auction), 3 ether);

        vm.prank(address(auction));
        operatorBond.slashNonLiveness(sid, 1);

        _closeAfterDeadline(sid, auction);

        uint256 treasuryBefore = address(treasury).balance;
        operatorBond.settleSlash(sid);
        assertEq(address(treasury).balance - treasuryBefore, 3 ether, "K-06: whole pool to Treasury (no victims)");

        vm.prank(operator1);
        vm.expectRevert(AgentBond.NothingToWithdraw.selector);
        operatorBond.withdraw(sid);
    }

    /// K-07: withdraw before the session closes reverts SessionNotClosed. The close gate stops an operator
    ///       draining its stake ahead of any future recordClaim (which would leave the victim paid zero).
    function test_RevertWhen_WithdrawBeforeSessionClosed() public {
        vm.deal(operator1, 5 ether);
        vm.prank(operator1);
        operatorBond.deposit{value: 5 ether}(sid, address(auction), 5 ether);

        vm.prank(operator1);
        vm.expectRevert(AgentBond.SessionNotClosed.selector);
        operatorBond.withdraw(sid);
    }

    /// K-08: a session's slash + victim claims never draw down another session's stake from the shared
    ///       singleton balance. Session A is fully slashed (victim + Treasury remainder); session B's
    ///       independent stake stays intact and fully reclaimable.
    function test_CrossSessionPoolIsolationOnSlash() public {
        bytes32 sidB = keccak256("SESSION_B");

        // A second real clone owns session B so it closes/withdraws through the session-bound,
        // deadline-gated closeSession.
        SessionAuction auctionB = SessionAuction(Clones.clone(address(impl)));
        InitConfig memory cfgB = _defaultInitConfig(address(0));
        cfgB.sessionId = sidB;
        vm.prank(address(hammer));
        auctionB.initialize(cfgB);
        operatorBond.registerClone(address(auctionB));

        // op1 stakes 10 on session A, op2 stakes 5 on session B, both held by the same singleton.
        vm.deal(operator1, 10 ether);
        vm.prank(operator1);
        operatorBond.deposit{value: 10 ether}(sid, address(auction), 10 ether);
        vm.deal(operator2, 5 ether);
        vm.prank(operator2);
        operatorBond.deposit{value: 5 ether}(sidB, address(auctionB), 5 ether);

        assertEq(address(operatorBond).balance, 15 ether, "K-08: singleton holds both sessions' stake");

        // Fully slash session A: 3 to a recorded victim, 7 remainder to Treasury.
        vm.prank(address(auction));
        operatorBond.recordClaim(sid, bidder1, 3 ether);
        _closeAfterDeadline(sid, auction);
        operatorBond.settleSlash(sid);
        vm.prank(bidder1);
        operatorBond.claimSlash(sid);

        // Session B's stake is untouched by A's full slash + claim (no cross-session draw).
        assertEq(address(operatorBond).balance, 5 ether, "K-08: session B stake intact after A fully slashed");
        assertEq(operatorBond.bondOf(sidB), 5 ether, "K-08: session B pool intact");

        // Session B's operator still reclaims its full stake.
        _closeAfterDeadline(sidB, auctionB);
        uint256 before = operator2.balance;
        vm.prank(operator2);
        operatorBond.withdraw(sidB);
        assertEq(operator2.balance - before, 5 ether, "K-08: session B operator reclaims full stake");
        assertEq(address(operatorBond).balance, 0, "K-08: singleton conserved across both sessions");
    }

    /// K-09: closeSession is permissionless but reverts SessionNotClosed before the session's verifiable
    ///       bondClaimsCloseAt, so it can never fire while a victim's harm can still land.
    function test_RevertWhen_CloseBeforeDeadline() public {
        vm.deal(operator1, 5 ether);
        vm.prank(operator1);
        operatorBond.deposit{value: 5 ether}(sid, address(auction), 5 ether);

        // block.timestamp is well before auction.bondClaimsCloseAt(), so the close is rejected.
        vm.expectRevert(AgentBond.SessionNotClosed.selector);
        operatorBond.closeSession(sid, address(auction));
    }

    /// K-10: a registered clone can only close the session it owns. Closing a foreign sessionId through a
    ///       clone whose sessionId() differs reverts Unauthorized, mirroring recordClaim/slashNonLiveness.
    function test_RevertWhen_CloseForeignSession() public {
        vm.warp(auction.bondClaimsCloseAt()); // even past the deadline, the session binding must hold
        // `auction` owns `sid`, not keccak256("FOREIGN").
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        operatorBond.closeSession(keccak256("FOREIGN"), address(auction));
    }

    /// K-11: once a session is closed the claim ledger is sealed; a late recordClaim reverts
    ///       SessionAlreadyClosed, so no harm can land after operators become eligible to withdraw.
    function test_RevertWhen_RecordClaimAfterClose() public {
        vm.deal(operator1, 5 ether);
        vm.prank(operator1);
        operatorBond.deposit{value: 5 ether}(sid, address(auction), 5 ether);

        _closeAfterDeadline(sid, auction);

        vm.prank(address(auction));
        vm.expectRevert(AgentBond.SessionAlreadyClosed.selector);
        operatorBond.recordClaim(sid, bidder1, 1 ether);
    }

    /// @dev Deploy + register a fresh ERC-20-rail session clone (paymentToken == token) bound to `s`.
    function _erc20Session(bytes32 s) private returns (SessionAuction a) {
        a = SessionAuction(Clones.clone(address(impl)));
        InitConfig memory cfg = _defaultInitConfig(address(token));
        cfg.sessionId = s;
        vm.prank(address(hammer));
        a.initialize(cfg);
        operatorBond.registerClone(address(a));
    }

    /// @dev Stake `amt` of the session's ERC-20 from `op` (approve + deposit on the token rail).
    function _stakeToken(address op, uint256 amt, bytes32 s, SessionAuction clone) private {
        token.mint(op, amt);
        vm.prank(op);
        token.approve(address(operatorBond), amt);
        vm.prank(op);
        operatorBond.deposit(s, address(clone), amt); // ERC-20: no msg.value, amount pulled
    }

    /// K-12: the ERC-20 bond rail. An operator stakes the session's ERC-20; a slash distributes the TOKEN
    ///       pro-rata to the victim with the remainder to Treasury, and the token pool conserves to the unit
    ///       (10 in == 3 victim + 7 Treasury out).
    function test_Erc20BondSlashDistributesAndConserves() public {
        bytes32 sidE = keccak256("SESSION_ERC20");
        SessionAuction auctionE = _erc20Session(sidE);
        _stakeToken(operator1, 10e6, sidE, auctionE);
        assertEq(operatorBond.bondOf(sidE), 10e6, "K-12: token stake pooled");
        assertEq(operatorBond.sessionToken(sidE), address(token), "K-12: session rail is the ERC-20");
        assertEq(token.balanceOf(address(operatorBond)), 10e6, "K-12: token held by the bond");

        // Record a 3-unit harm victim through the real onlyAuction + session-binding gate (the ERC-20
        // clone is the caller).
        vm.prank(address(auctionE));
        operatorBond.recordClaim(sidE, bidder1, 3e6);

        _closeAfterDeadline(sidE, auctionE);

        uint256 treasuryBefore = token.balanceOf(address(treasury));
        operatorBond.settleSlash(sidE);
        assertEq(token.balanceOf(address(treasury)) - treasuryBefore, 7e6, "K-12: token remainder to Treasury");

        uint256 victimBefore = token.balanceOf(bidder1);
        vm.prank(bidder1);
        operatorBond.claimSlash(sidE);
        assertEq(token.balanceOf(bidder1) - victimBefore, 3e6, "K-12: victim paid token harm pro-rata");
        assertEq(token.balanceOf(address(operatorBond)), 0, "K-12: token bond fully distributed (conserved)");
    }

    /// K-13: a clean ERC-20 session returns the operator's full TOKEN stake on close + withdraw.
    function test_Erc20CleanWithdrawReturnsFullTokenStake() public {
        bytes32 sidE = keccak256("SESSION_ERC20_CLEAN");
        SessionAuction auctionE = _erc20Session(sidE);
        _stakeToken(operator1, 7e6, sidE, auctionE);

        _closeAfterDeadline(sidE, auctionE);

        uint256 before = token.balanceOf(operator1);
        vm.prank(operator1);
        operatorBond.withdraw(sidE);
        assertEq(token.balanceOf(operator1) - before, 7e6, "K-13: clean ERC-20 withdraw returns full token stake");
        assertEq(operatorBond.bondOf(sidE), 0, "K-13: token pool drained on withdraw");
    }

    /// K-14: cross-denomination isolation on the shared singleton. A NATIVE session fully slashed does not
    ///       touch an ERC-20 session's token pool, and vice-versa; each settles in its own rail.
    function test_CrossDenominationIsolation() public {
        // Native session A (the canonical `auction`/sid): op1 stakes 10 ether.
        vm.deal(operator1, 10 ether);
        vm.prank(operator1);
        operatorBond.deposit{value: 10 ether}(sid, address(auction), 10 ether);

        // ERC-20 session E: op2 stakes 8 token units.
        bytes32 sidE = keccak256("SESSION_ERC20_ISO");
        SessionAuction auctionE = _erc20Session(sidE);
        _stakeToken(operator2, 8e6, sidE, auctionE);

        assertEq(address(operatorBond).balance, 10 ether, "K-14: native balance = native stake only");
        assertEq(token.balanceOf(address(operatorBond)), 8e6, "K-14: token balance = token stake only");

        // Fully slash the NATIVE session A.
        vm.prank(address(auction));
        operatorBond.recordClaim(sid, bidder1, 3 ether);
        _closeAfterDeadline(sid, auction);
        operatorBond.settleSlash(sid);
        vm.prank(bidder1);
        operatorBond.claimSlash(sid);

        // The ERC-20 pool is UNTOUCHED by the native slash (no cross-denomination draw).
        assertEq(token.balanceOf(address(operatorBond)), 8e6, "K-14: ERC-20 pool intact after native slash");
        assertEq(operatorBond.bondOf(sidE), 8e6, "K-14: ERC-20 session pool intact");
        assertEq(address(operatorBond).balance, 0, "K-14: native rail fully distributed");

        // The ERC-20 operator still reclaims its full token stake.
        _closeAfterDeadline(sidE, auctionE);

        uint256 before = token.balanceOf(operator2);
        vm.prank(operator2);
        operatorBond.withdraw(sidE);
        assertEq(token.balanceOf(operator2) - before, 8e6, "K-14: ERC-20 operator reclaims full token stake");
    }

    /// K-15: a fee-on-transfer token credits the measured received amount, not the requested amount, so the
    ///       pool is never over-credited beyond what actually arrived.
    function test_Erc20FeeOnTransferCreditsReceivedNotRequested() public {
        K_FeeOnTransferToken feeToken = new K_FeeOnTransferToken();

        bytes32 sidF = keccak256("SESSION_FEE");
        SessionAuction auctionF = SessionAuction(Clones.clone(address(impl)));
        InitConfig memory cfgF = _defaultInitConfig(address(feeToken));
        cfgF.sessionId = sidF;
        vm.prank(address(hammer));
        auctionF.initialize(cfgF);
        operatorBond.registerClone(address(auctionF));

        uint256 requested = 100e6;
        feeToken.mint(operator1, requested);
        vm.prank(operator1);
        feeToken.approve(address(operatorBond), requested);
        vm.prank(operator1);
        operatorBond.deposit(sidF, address(auctionF), requested);

        uint256 received = requested - requested / 100; // 1% fee burned in transfer
        assertEq(operatorBond.bondOf(sidF), received, "K-15: bond credits the MEASURED received amount, not requested");
        assertEq(feeToken.balanceOf(address(operatorBond)), received, "K-15: pool == actual token balance held");
    }

    /// K-16: a victim harmed on multiple distinct seqs is paid the sum of its recorded harms, not the
    ///       single largest.
    function test_RecordClaimSumsMultiSeqHarm() public {
        vm.deal(operator1, 10 ether);
        vm.prank(operator1);
        operatorBond.deposit{value: 10 ether}(sid, address(auction), 10 ether);

        // Same victim, two distinct harm events recorded through the real onlyAuction + session-binding
        // gate (the `auction` clone); the recorded harms accumulate rather than taking the max.
        vm.prank(address(auction));
        operatorBond.recordClaim(sid, bidder1, 5 ether);
        vm.prank(address(auction));
        operatorBond.recordClaim(sid, bidder1, 2 ether);

        _closeAfterDeadline(sid, auction);
        operatorBond.settleSlash(sid);

        uint256 before = bidder1.balance;
        vm.prank(bidder1);
        operatorBond.claimSlash(sid);
        assertEq(bidder1.balance - before, 7 ether, "M1: victim paid SUM of harms (5+2 = 7), not max(5)");
    }
}

/// @dev A fee-on-transfer ERC-20 (1% burned on every transfer) that proves AgentBond credits the
///      measured received amount, not the requested amount. Production's paymentToken allowlist bars
///      such tokens, so this exercises a path the allowlist normally prevents.
contract K_FeeOnTransferToken is ERC20 {
    constructor() ERC20("FeeToken", "FEE") {}

    function mint(address to, uint256 amount) external {
        _mint(to, amount);
    }

    function _update(address from, address to, uint256 value) internal override {
        if (from != address(0) && to != address(0)) {
            uint256 fee = value / 100; // 1% fee
            super._update(from, to, value - fee); // recipient receives less than `value`
            if (fee != 0) super._update(from, address(0xdEaD), fee);
        } else {
            super._update(from, to, value); // mint/burn unchanged
        }
    }
}
