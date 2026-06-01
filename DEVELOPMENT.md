# Hammer contracts: local development

Everything you need to run a local chain, load faux funds, and inspect transactions.
Foundry (forge, cast, anvil, chisel) is already installed at `~/.foundry/bin`. Run
`make help` to list the convenience commands.

No em dashes by product-owner preference.

## 1. Run a local chain

```sh
make anvil
```

`anvil` starts a local Ethereum node at `http://127.0.0.1:8545` (chain id 31337). On
startup it prints 10 dev accounts, each prefunded with 10000 faux ETH, with their
private keys and the seed mnemonic. Account 0 is:

```
addr: 0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266
key:  0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
```

These keys are public and well-known. They are for LOCAL use only; never send real
funds to them.

Variants:
- `make anvil-trace` prints a full execution trace for every transaction (loud but great for debugging).
- `make anvil-fork` forks Arbitrum Sepolia (set `ARB_SEPOLIA_RPC` in `.env` first), so you test against real on-chain state and the real RIP-7212 P256 precompile behavior.

Leave anvil running in one terminal; run the commands below in another.

## 2. Load faux funds

### Native ETH

The 10 anvil accounts already hold 10000 ETH each. To top up any address to 100 ETH:

```sh
make fund-eth ADDR=0xYourAddress
```

(Under the hood: `cast rpc anvil_setBalance <addr> <wei>`, an anvil-only cheat.)

### Faux ERC-20 (for the configurable-denomination path, e.g. USDC)

There is a test-only token at `test/mocks/MockERC20.sol` with an unrestricted `mint`.

```sh
# 1. deploy a 6-decimal faux USDC; note the printed "Deployed to:" address
make deploy-usdc

# 2. mint 1000 USDC (6 decimals => 1000 * 1e6 = 1000000000) to an address
make mint-usdc TOKEN=0xDeployedToken TO=0xRecipient AMT=1000000000
```

When you eventually run a `SessionAuction` with `paymentToken` set to this token, bidders
`approve` the auction and then `depositCeiling` pulls via `SafeERC20`.

### Faux ERC-20 inside Foundry tests (no deploy needed)

In Solidity tests you do not deploy or mint manually. Use forge-std cheatcodes:

```solidity
import {Test} from "forge-std/Test.sol";
// give `user` 1000 USDC of an already-deployed token (works on forks too, via storage writes):
deal(address(usdc), user, 1000e6);
// give `user` 100 native ETH:
vm.deal(user, 100 ether);
```

`deal` is the idiomatic way to fund test actors; the MockERC20 + `make mint-usdc` path is for
poking at a live local anvil by hand or from a front-end.

## 3. Inspect transactions

Every command takes the tx hash that `cast send` / your scripts print.

```sh
make receipt TX=0xHash     # status, gas used, block, all logs
make trace   TX=0xHash     # cast run: replay the tx and print the full call trace
make logs    TX=0xHash     # decoded event logs (needs jq)
make tx      TX=0xHash     # raw tx fields (from, to, input, value, nonce)
make balance ADDR=0xAddr   # ETH balance in ether
make block                 # latest block summary
```

`make trace` (`cast run`) is the most useful: it re-executes the transaction locally and
shows every internal call, revert reason, and event, which is how you debug a failed
`placeBid` or a fund-routing path. Add `-vvvv` to a `forge test` run for the same trace on
test transactions.

Read calls without sending a tx:

```sh
cast call 0xContract "getLot(uint256)" 42 --rpc-url http://127.0.0.1:8545
cast send 0xContract "depositCeiling(uint256,uint256)" 42 1000000000 \
  --rpc-url http://127.0.0.1:8545 --private-key 0xac09...ff80
```

## 4. A visual block explorer (optional)

If you prefer a UI over `cast`, run Otterscan (a local explorer) against anvil. Docker is
installed:

```sh
docker run --rm -p 5100:80 --name otterscan \
  -e ERIGON_URL="http://host.docker.internal:8545" otterscan/otterscan:latest
```

Open http://localhost:5100. It shows blocks, transactions, traces, and token transfers from
your local anvil. (Otterscan expects the `ots_` trace RPCs, which anvil supports.) Stop it
with `docker stop otterscan`.

## 5. Typical loop

```sh
# terminal 1
make anvil

# terminal 2
make build            # compile (currently only the MockERC20 + forge-std)
make test             # run the suite (none yet; comes after architecture sign-off)
make deploy-usdc      # if you want a faux token to play with
# ... deploy a contract, send a tx, then:
make trace TX=0xHash  # see exactly what happened
```

## 6. Status of this environment

- Toolchain: Foundry 1.7.1 (forge/cast/anvil/chisel), pinned solc 0.8.28, `evm_version = cancun`.
- Dependencies: `forge-std` and OpenZeppelin v5.6.1 as git submodules under `lib/`.
- Config: `foundry.toml` (optimizer, via_ir, fuzz/invariant profiles, Arbitrum RPC + Etherscan blocks), `remappings.txt`, `.env.example`.
- Present now: this Makefile, the `MockERC20` test token, and the design docs under `docs/`.
- Not present yet: the protocol contracts (`SessionAuction`, `PaddleRegistry`, `FlagRegistry`, `Treasury`, `AgentBond`, `Hammer` factory) and the e2e suite. Those are the implementation pass, which begins after the two PRIV decisions are signed off (see `docs/00-review-findings.md` closeout).

Available Accounts
==================

(0) 0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266 (10000.000000000000000000 ETH)
(1) 0x70997970C51812dc3A010C7d01b50e0d17dc79C8 (10000.000000000000000000 ETH)
(2) 0x3C44CdDdB6a900fa2b585dd299e03d12FA4293BC (10000.000000000000000000 ETH)
(3) 0x90F79bf6EB2c4f870365E785982E1f101E93b906 (10000.000000000000000000 ETH)
(4) 0x15d34AAf54267DB7D7c367839AAf71A00a2C6A65 (10000.000000000000000000 ETH)
(5) 0x9965507D1a55bcC2695C58ba16FB37d819B0A4dc (10000.000000000000000000 ETH)
(6) 0x976EA74026E726554dB657fA54763abd0C3a0aa9 (10000.000000000000000000 ETH)
(7) 0x14dC79964da2C08b23698B3D3cc7Ca32193d9955 (10000.000000000000000000 ETH)
(8) 0x23618e81E3f5cdF7f54C3d65f7FBc0aBf5B21E8f (10000.000000000000000000 ETH)
(9) 0xa0Ee7A142d267C1f36714E4a8F75612F20a79720 (10000.000000000000000000 ETH)

Private Keys
==================

(0) 0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
(1) 0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d
(2) 0x5de4111afa1a4b94908f83103eb1f1706367c2e68ca870fc3fb9a804cdab365a
(3) 0x7c852118294e51e653712a81e05800f419141751be58f605c371e15141b007a6
(4) 0x47e179ec197488593b187f80a00eb0da91f1b9d0b13f8733639f19c30a34926a
(5) 0x8b3a350cf5c34c9194ca85829a2df0ec3153be0318b5e2d3348e872092edffba
(6) 0x92db14e403b83dfe3df233f83dfa3a0d7096f21ca9b0d6d6b8d88b2b4ec1564e
(7) 0x4bbbf85ce3377467afe5d46f804f221813b2bb87f24d81f60f1fcdbf7cbf4356
(8) 0xdbda1821b80551c9d65939329250298aa3472ba22feea921c0cf5d620ea67b97
(9) 0x2a871d0798f97d79848a013d4936a73bf4cc922c825d33c1cf7073dff6d409c6

Wallet
==================
Mnemonic:          test test test test test test test test test test test junk
Derivation path:   m/44'/60'/0'/0/
