// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.21;

interface IRateProviderLike {
    function getConversionRate() external view returns (uint256);
}

interface IERC20 {

    function transfer(address recipient, uint256 amount) external returns (bool success);

    function transferFrom(address owner, address recipient, uint256 amount)
        external returns (bool success);
}

library Math {
    function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
        if (b == 0) {
            // Guarantee the same behavior as in a regular Solidity division.
            return a / b;
        }

        // (a + b - 1) / b can overflow on addition, so we distribute.
        return a == 0 ? 0 : (a - 1) / b + 1;
    }
}

contract Psm3Mock {

    uint256 internal _usdcPrecision;
    uint256 internal _usdsPrecision;
    uint256 internal _susdsPrecision;

    IERC20 public usdc;
    IERC20 public usds;
    IERC20 public susds;

    address public rateProvider;

    address public pocket;

    uint256 public totalShares;

    mapping(address user => uint256 shares) public shares;

    function swapExactIn(
        address assetIn,
        address assetOut,
        uint256 amountIn,
        uint256 minAmountOut,
        address receiver,
        uint256
    )
        external returns (uint256 amountOut)
    {
        require(amountIn != 0,          "PSM3/invalid-amountIn");
        require(receiver != address(0), "PSM3/invalid-receiver");

        amountOut = previewSwapExactIn(assetIn, assetOut, amountIn);

        require(amountOut >= minAmountOut, "PSM3/amountOut-too-low");

        _pullAsset(assetIn, amountIn);
        _pushAsset(assetOut, receiver, amountOut);
    }

    function swapExactOut(
        address assetIn,
        address assetOut,
        uint256 amountOut,
        uint256 maxAmountIn,
        address receiver,
        uint256
    )
        external returns (uint256 amountIn)
    {
        require(amountOut != 0,         "PSM3/invalid-amountOut");
        require(receiver != address(0), "PSM3/invalid-receiver");

        amountIn = previewSwapExactOut(assetIn, assetOut, amountOut);

        require(amountIn <= maxAmountIn, "PSM3/amountIn-too-high");

        _pullAsset(assetIn, amountIn);
        _pushAsset(assetOut, receiver, amountOut);
    }

    function previewSwapExactIn(address assetIn, address assetOut, uint256 amountIn)
        public view returns (uint256 amountOut)
    {
        // Round down to get amountOut
        amountOut = _getSwapQuote(assetIn, assetOut, amountIn, false);
    }

    function previewSwapExactOut(address assetIn, address assetOut, uint256 amountOut)
        public view returns (uint256 amountIn)
    {
        // Round up to get amountIn
        amountIn = _getSwapQuote(assetOut, assetIn, amountOut, true);
    }

    function _getSwapQuote(address asset, address quoteAsset, uint256 amount, bool roundUp)
        internal view returns (uint256 quoteAmount)
    {
        if (asset == address(usdc)) {
            if      (quoteAsset == address(usds))  return _convertOneToOne(amount, _usdcPrecision, _usdsPrecision, roundUp);
            else if (quoteAsset == address(susds)) return _convertToSUsds(amount, _usdcPrecision, roundUp);
        }

        else if (asset == address(usds)) {
            if      (quoteAsset == address(usdc))  return _convertOneToOne(amount, _usdsPrecision, _usdcPrecision, roundUp);
            else if (quoteAsset == address(susds)) return _convertToSUsds(amount, _usdsPrecision, roundUp);
        }

        else if (asset == address(susds)) {
            if      (quoteAsset == address(usdc)) return _convertFromSUsds(amount, _usdcPrecision, roundUp);
            else if (quoteAsset == address(usds)) return _convertFromSUsds(amount, _usdsPrecision, roundUp);
        }

        revert("PSM3/invalid-asset");
    }

    function _convertToSUsds(uint256 amount, uint256 assetPrecision, bool roundUp) internal view returns (uint256) {
        uint256 rate = IRateProviderLike(rateProvider).getConversionRate();

        if (!roundUp) return amount * 1e27 / rate * _susdsPrecision / assetPrecision;

        return Math.ceilDiv(
            Math.ceilDiv(amount * 1e27, rate) * _susdsPrecision,
            assetPrecision
        );
    }

    function _convertFromSUsds(uint256 amount, uint256 assetPrecision, bool roundUp) internal view returns (uint256) {
        uint256 rate = IRateProviderLike(rateProvider).getConversionRate();

        if (!roundUp) return amount * rate / 1e27 * assetPrecision / _susdsPrecision;

        return Math.ceilDiv(
            Math.ceilDiv(amount * rate, 1e27) * assetPrecision,
            _susdsPrecision
        );
    }

    function _convertOneToOne(
        uint256 amount,
        uint256 assetPrecision,
        uint256 convertAssetPrecision,
        bool roundUp
    ) internal pure returns (uint256) {
        if (!roundUp) return amount * convertAssetPrecision / assetPrecision;

        return Math.ceilDiv(amount * convertAssetPrecision, assetPrecision);
    }

    function _getAssetCustodian(address asset) internal view returns (address custodian) {
        custodian = asset == address(usdc) ? pocket : address(this);
    }

    function _pullAsset(address asset, uint256 amount) internal {
        IERC20(asset).transferFrom(msg.sender, _getAssetCustodian(asset), amount);
    }

    function _pushAsset(address asset, address receiver, uint256 amount) internal {
        if (asset == address(usdc) && pocket != address(this)) {
            usdc.transferFrom(pocket, receiver, amount);
        } else {
            IERC20(asset).transfer(receiver, amount);
        }
    }
}
