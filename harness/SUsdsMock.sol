// SPDX-License-Identifier: AGPL-3.0-or-later

pragma solidity ^0.8.21;

interface GemLike {
    function transfer(address, uint256) external;
    function transferFrom(address, address, uint256) external;
}

contract SUsdsMock {

    // ERC20
    uint256                                           public totalSupply;
    mapping (address => uint256)                      public balanceOf;
    mapping (address => mapping (address => uint256)) public allowance;

    // Savings yield
    uint192 public chi;   // The Rate Accumulator  [ray]
    uint64  public rho;   // Time of last drip     [unix epoch time]
    uint256 public ssr;   // The USDS Savings Rate [ray]

    // Math
    uint256 private constant RAY = 10 ** 27;

    GemLike public usds;

    // Math

    function _rpow(uint256 x, uint256 n) internal pure returns (uint256 z) {
        assembly {
            switch x case 0 {switch n case 0 {z := RAY} default {z := 0}}
            default {
                switch mod(n, 2) case 0 { z := RAY } default { z := x }
                let half := div(RAY, 2)  // for rounding.
                for { n := div(n, 2) } n { n := div(n,2) } {
                    let xx := mul(x, x)
                    if iszero(eq(div(xx, x), x)) { revert(0,0) }
                    let xxRound := add(xx, half)
                    if lt(xxRound, xx) { revert(0,0) }
                    x := div(xxRound, RAY)
                    if mod(n,2) {
                        let zx := mul(z, x)
                        if and(iszero(iszero(x)), iszero(eq(div(zx, x), z))) { revert(0,0) }
                        let zxRound := add(zx, half)
                        if lt(zxRound, zx) { revert(0,0) }
                        z := div(zxRound, RAY)
                    }
                }
            }
        }
    }

    function _divup(uint256 x, uint256 y) internal pure returns (uint256 z) {
        // Note: _divup(0,0) will return 0 differing from natural solidity division
        unchecked {
            z = x != 0 ? ((x - 1) / y) + 1 : 0;
        }
    }

    // --- ERC20 Mutations ---

    function approve(address spender, uint256 value) external returns (bool) {
        allowance[msg.sender][spender] = value;
        return true;
    }

    function transfer(address to, uint256 value) external returns (bool) {
        require(to != address(0) && to != address(this), "SUsds/invalid-address");
        uint256 balance = balanceOf[msg.sender];
        require(balance >= value, "SUsds/insufficient-balance");

        balanceOf[msg.sender] = balance - value;
        balanceOf[to] += value; // note: we don't need an overflow check here b/c sum of all balances == totalSupply

        return true;
    }

    function transferFrom(address from, address to, uint256 value) external returns (bool) {
        uint256 balance = balanceOf[from];
        require(balance >= value, "SUsds/insufficient-balance");

        if (from != msg.sender) {
            uint256 allowed = allowance[from][msg.sender];
            if (allowed != type(uint256).max) {
                require(allowed >= value, "SUsds/insufficient-allowance");

                allowance[from][msg.sender] = allowed - value;
            }
        }

        balanceOf[from] = balance - value;
        balanceOf[to] += value;
        return true;
    }

    // --- Mint/Burn Internal ---

    function _mint(uint256 assets, uint256 shares, address receiver) internal {
        require(receiver != address(0) && receiver != address(this), "invalid-address");

        usds.transferFrom(msg.sender, address(this), assets);

        balanceOf[receiver] = balanceOf[receiver] + shares;
        totalSupply = totalSupply + shares;
    }

    function _burn(uint256 assets, uint256 shares, address receiver, address owner) internal {
        uint256 balance = balanceOf[owner];
        require(balance >= shares, "SUsds/insufficient-balance");

        if (owner != msg.sender) {
            uint256 allowed = allowance[owner][msg.sender];
            if (allowed != type(uint256).max) {
                require(allowed >= shares, "SUsds/insufficient-allowance");

                allowance[owner][msg.sender] = allowed - shares;
            }
        }

        balanceOf[owner] = balance - shares;
        totalSupply      = totalSupply - shares;

        usds.transfer(receiver, assets);
    }

    function convertToShares(uint256 assets) public view returns (uint256) {
        return assets * RAY / chi;
    }

    function convertToAssets(uint256 shares) public view returns (uint256) {
        return shares * chi / RAY;
    }

    function previewDeposit(uint256 assets) external view returns (uint256) {
        return convertToShares(assets);
    }

    function deposit(uint256 assets, address receiver) public returns (uint256 shares) {
        shares = assets * RAY / chi;
        _mint(assets, shares, receiver);
    }

    function maxMint(address) external pure returns (uint256) {
        return type(uint256).max;
    }

    function previewMint(uint256 shares) external view returns (uint256) {
        return _divup(shares * chi, RAY);
    }

    function mint(uint256 shares, address receiver) public returns (uint256 assets) {
        assets = _divup(shares * chi, RAY);
        _mint(assets, shares, receiver);
    }

    function previewWithdraw(uint256 assets) external view returns (uint256) {
        return _divup(assets * RAY, chi);
    }

    function withdraw(uint256 assets, address receiver, address owner) external returns (uint256 shares) {
        shares = _divup(assets * RAY, chi);
        _burn(assets, shares, receiver, owner);
    }

    function maxRedeem(address owner) external view returns (uint256) {
        return balanceOf[owner];
    }

    function previewRedeem(uint256 shares) external view returns (uint256) {
        return convertToAssets(shares);
    }

    function redeem(uint256 shares, address receiver, address owner) external returns (uint256 assets) {
        assets = shares * chi / RAY;
        _burn(assets, shares, receiver, owner);
    }
}
