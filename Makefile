# Hammer contracts: common dev commands.
# Foundry binaries live in ~/.foundry/bin; put them on PATH so `make` finds them
# regardless of which shell invoked it (make uses /bin/sh, which does not source
# your fish/zsh profile).
export PATH := $(HOME)/.foundry/bin:$(PATH)

# Local anvil defaults. Override on the command line, e.g. `make receipt RPC=... TX=0x...`.
RPC ?= http://127.0.0.1:8545
# anvil's first prefabricated dev account (well-known key, LOCAL ONLY, never use on a real net).
DEV_PK ?= 0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
DEV_ADDR ?= 0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266

# Contracts whose storage layout is frozen and drift-checked. SessionAuction is the EIP-1167 clone
# implementation (its layout must stay stable); the rest are deployed-once singletons.
STORAGE_CONTRACTS := SessionAuction AgentBond Treasury FlagRegistry
# Normalize `type`: strip the AST-node ids / array lengths that shift on any code edit but do not change
# the real layout, so a genuine slot/offset move trips the check while an ordinary logic edit does not.
STORAGE_FILTER := [.storage[] | {label, slot, offset, type: (.type | gsub("[0-9]+_storage"; "_storage"))}]

.DEFAULT_GOAL := help

## ---- build / test ----------------------------------------------------------

build: ## Compile contracts
	forge build

test: ## Run all tests (verbose)
	forge test -vvv

test-gas: ## Run tests with a gas report
	forge test --gas-report

snapshot: ## Write a gas snapshot (.gas-snapshot) for regression tracking
	forge snapshot

coverage: ## Line coverage report
	forge coverage

fmt: ## Format Solidity
	forge fmt

fmt-check: ## Check formatting (CI)
	forge fmt --check

clean: ## Remove build artifacts
	forge clean

## ---- storage layout --------------------------------------------------------

storage: ## Regenerate the committed storage-layout baselines (storage-layout/<C>.json)
	@for c in $(STORAGE_CONTRACTS); do \
		forge inspect "$$c" storageLayout --json | jq -S '$(STORAGE_FILTER)' > "storage-layout/$$c.json"; \
		echo "  regenerated storage-layout/$$c.json"; \
	done

storage-check: ## Verify storage layout matches the committed baselines; fails on drift (CI)
	@set -e; for c in $(STORAGE_CONTRACTS); do \
		forge inspect "$$c" storageLayout --json | jq -S '$(STORAGE_FILTER)' > "/tmp/$$c.layout.json"; \
		if ! diff -u "storage-layout/$$c.json" "/tmp/$$c.layout.json"; then \
			echo "storage-layout drift in $$c; if intentional, run: make storage"; \
			exit 1; \
		fi; \
	done
	@echo "storage layout matches the committed baselines"

## ---- local chain -----------------------------------------------------------

anvil: ## Start a local chain (10 accounts prefunded with 10000 ETH; prints keys)
	anvil

anvil-trace: ## Local chain that prints full execution traces for every tx
	anvil --steps-tracing

anvil-fork: ## Local chain forking Arbitrum Sepolia (reads ARB_SEPOLIA_RPC from .env)
	@test -f .env || (echo "copy .env.example to .env and fill ARB_SEPOLIA_RPC" && exit 1)
	. ./.env && anvil --fork-url $$ARB_SEPOLIA_RPC

## ---- faux funds (local anvil only) -----------------------------------------

fund-eth: ## Give ADDR 100 faux ETH. Usage: make fund-eth ADDR=0x...
	cast rpc anvil_setBalance $(ADDR) 0x56BC75E2D63100000 --rpc-url $(RPC)

deploy-usdc: ## Deploy a 6-decimal faux USDC (MockERC20) from the dev account; prints its address
	forge create test/mocks/MockERC20.sol:MockERC20 \
		--rpc-url $(RPC) --private-key $(DEV_PK) --broadcast \
		--constructor-args "USD Coin" "USDC" 6

mint-usdc: ## Mint faux USDC. Usage: make mint-usdc TOKEN=0x.. TO=0x.. AMT=1000000000 (1000 USDC at 6dp)
	cast send $(TOKEN) "mint(address,uint256)" $(TO) $(AMT) --rpc-url $(RPC) --private-key $(DEV_PK)

## ---- inspect transactions --------------------------------------------------

balance: ## ETH balance of ADDR. Usage: make balance ADDR=0x...
	cast balance $(ADDR) --rpc-url $(RPC) --ether

receipt: ## Full receipt (status, gas, logs) of a tx. Usage: make receipt TX=0x...
	cast receipt $(TX) --rpc-url $(RPC)

trace: ## Replay a tx and print the full call trace. Usage: make trace TX=0x...
	cast run $(TX) --rpc-url $(RPC)

logs: ## Decode all logs of a tx. Usage: make logs TX=0x...
	cast receipt $(TX) --rpc-url $(RPC) --json | jq '.logs'

tx: ## Raw tx fields. Usage: make tx TX=0x...
	cast tx $(TX) --rpc-url $(RPC)

block: ## Latest block summary
	cast block latest --rpc-url $(RPC)

help: ## List targets
	@grep -hE '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "  \033[36m%-14s\033[0m %s\n", $$1, $$2}'

.PHONY: build test test-gas snapshot coverage fmt fmt-check clean storage storage-check anvil anvil-trace anvil-fork fund-eth deploy-usdc mint-usdc balance receipt trace logs tx block help
