// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.21;

contract RateProviderMock {
    uint256 rate;

    function getConversionRate() external view returns (uint256) {
        return rate;
    }
}
