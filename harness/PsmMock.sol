// SPDX-License-Identifier: AGPL-3.0-or-later

pragma solidity ^0.8.16;

interface GemLike {
    function balanceOf(address) external view returns (uint256);
    function decimals() external view returns (uint8);
    function approve(address, uint256) external;
    function transfer(address, uint256) external;
    function transferFrom(address, address, uint256) external;
}

contract PsmMock {
    uint256 public constant HALTED = type(uint256).max;
    GemLike public gem;
    GemLike public dai;
    address public pocket;
    uint256 public tin;
    uint256 public tout;

    uint256 constant to18ConversionFactor = 10 ** 12;
    uint256 constant WAD = 10 ** 18;

    function sellGem(address usr, uint256 gemAmt) external returns (uint256 daiOutWad) {
        uint256 tin_ = tin;
        require(tin_ != HALTED, "sell-gem-halted");

        daiOutWad = gemAmt * to18ConversionFactor;
        uint256 fee;
        if (tin_ > 0) {
            fee = daiOutWad * tin_ / WAD;
            // At this point, `tin_ <= 1 WAD`, so an underflow is not possible.
            unchecked {
                daiOutWad -= fee;
            }
        }

        gem.transferFrom(msg.sender, pocket, gemAmt);
        // This can consume the whole balance including system fees not withdrawn.
        dai.transfer(usr, daiOutWad);
    }

    function buyGem(address usr, uint256 gemAmt) external returns (uint256 daiInWad) {
        uint256 tout_ = tout;
        require(tout_ != HALTED, "DssLitePsm/buy-gem-halted");

        daiInWad = gemAmt * to18ConversionFactor;
        uint256 fee;
        if (tout_ > 0) {
            fee = daiInWad * tout_ / WAD;
            daiInWad += fee;
        }

        dai.transferFrom(msg.sender, address(this), daiInWad);
        gem.transferFrom(pocket, usr, gemAmt);
    }
}
