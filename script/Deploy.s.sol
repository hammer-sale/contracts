// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

import {Script}   from "forge-std/Script.sol";
import {console2} from "forge-std/console2.sol";

import {PaddleRegistry} from "../src/PaddleRegistry.sol";
import {FlagRegistry}   from "../src/FlagRegistry.sol";
import {Treasury}       from "../src/Treasury.sol";
import {AgentBond}      from "../src/AgentBond.sol";
import {SessionAuction} from "../src/SessionAuction.sol";
import {Hammer}         from "../src/Hammer.sol";

/// @title Deploy
/// @notice Deploys the shared infrastructure once: the four singletons (PaddleRegistry, FlagRegistry,
///         Treasury, AgentBond), the locked SessionAuction implementation, and the Hammer factory, then
///         wires the factory and treasury so Hammer.createSession can register its per-session clones.
///         Sessions themselves are not created here: createSession(InitConfig) is a per-auction call that
///         needs the operator P-256 key, the pinned enclave measurement, and the session windows.
///
///         Run (Arbitrum Sepolia):
///           forge script script/Deploy.s.sol:Deploy --rpc-url arbitrum_sepolia --broadcast --verify
///         The broadcasting key (--private-key / --ledger / --account) becomes owner of the factory and
///         singletons.
contract Deploy is Script {
    function run()
        external
        returns (
            Hammer hammer,
            SessionAuction impl,
            Treasury treasury,
            AgentBond bond,
            PaddleRegistry paddles,
            FlagRegistry flags
        )
    {
        vm.startBroadcast();

        // Shared singletons: one set per deployment, reused across every session.
        paddles  = new PaddleRegistry(); // KYC paddle registry (ops-curated)
        flags    = new FlagRegistry();   // anti-collusion flag-root registry (ops-committed per session)
        treasury = new Treasury();       // forfeit + protocol-fee sink
        bond     = new AgentBond();      // per-session operator bond (native + ERC-20 rails)

        // Locked SessionAuction implementation: its constructor calls _disableInitializers, so the
        // implementation can never be initialized directly. Hammer EIP-1167-clones it and initializes
        // each clone per session.
        impl = new SessionAuction();

        // Factory: owns the implementation, then clones, initializes, and registers one auction per session.
        hammer = new Hammer(address(impl));

        // Wiring. createSession runs with msg.sender == hammer and calls registerClone on Treasury and
        // AgentBond, which admit only the owner or the wired factory, so the factory must be set on both.
        // AgentBond also needs the treasury as the sink for the slash remainder. PaddleRegistry and
        // FlagRegistry are read-only to the clone and need no wiring.
        treasury.setFactory(address(hammer));
        bond.setFactory(address(hammer));
        bond.setTreasury(address(treasury));

        vm.stopBroadcast();

        console2.log("Hammer factory  :", address(hammer));
        console2.log("SessionAuction  :", address(impl));
        console2.log("Treasury        :", address(treasury));
        console2.log("AgentBond       :", address(bond));
        console2.log("PaddleRegistry  :", address(paddles));
        console2.log("FlagRegistry    :", address(flags));
    }
}
