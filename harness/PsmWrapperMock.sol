// SPDX-License-Identifier: AGPL-3.0-or-later

pragma solidity ^0.8.21;

interface PsmLike {
    function tin() external returns (uint256);
    function tout() external returns (uint256);
    function sellGem(address, uint256) external returns (uint256);
    function buyGem(address, uint256) external returns (uint256);
}

interface GemLike {
    function transferFrom(address, address, uint256) external;
    function burn(address, uint256) external;
    function mint(address, uint256) external;
}

contract PsmWrapperMock {
    PsmLike      public   psm;
    GemLike      public   gem;
    GemLike      public   dai;
    GemLike      public   usds;

    uint256 constant to18ConversionFactor = 10**12;
    uint256 constant WAD = 10**18;

    function tin() external returns (uint256) {
        return psm.tin();
    }

    function tout() external returns (uint256) {
        return psm.tout();
    }

    function sellGem(address usr, uint256 gemAmt) external returns (uint256 usdsOutWad) {
        gem.transferFrom(msg.sender, address(this), gemAmt);
        usdsOutWad = psm.sellGem(address(this), gemAmt);
        dai.burn(address(this), usdsOutWad);
        usds.mint(usr, usdsOutWad);
    }

    function buyGem(address usr, uint256 gemAmt) external returns (uint256 usdsInWad) {
        uint256 gemAmt18 = gemAmt * to18ConversionFactor;
        usdsInWad = gemAmt18 + gemAmt18 * psm.tout() / WAD;
        usds.burn(msg.sender, usdsInWad);
        dai.mint(address(this), usdsInWad);
        psm.buyGem(usr, gemAmt);
    }
}
