// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

import {ERC20} from "@openzeppelin/contracts/token/ERC20/ERC20.sol";

/// @notice Test-only faux stablecoin for local development and for exercising
/// auctions denominated in a configurable ERC20. Has an unrestricted public
/// `mint`; never deploy to a real network.
contract MockERC20 is ERC20 {
    uint8 private immutable _customDecimals;

    /// @param decimals_ e.g. 6 to mimic USDC, 18 to mimic DAI.
    constructor(string memory name_, string memory symbol_, uint8 decimals_) ERC20(name_, symbol_) {
        _customDecimals = decimals_;
    }

    function decimals() public view override returns (uint8) {
        return _customDecimals;
    }

    /// @notice Mint faux funds to anyone, locally. Unrestricted on purpose.
    function mint(address to, uint256 amount) external {
        _mint(to, amount);
    }
}
