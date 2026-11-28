// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface IPrice {
    function price() external view returns (uint256);
}

contract TryCatch {
    function priceOr(IPrice o, uint256 dflt) external view returns (uint256) {
        try o.price() returns (uint256 p) {
            return p;
        } catch {
            return dflt;
        }
    }
}
