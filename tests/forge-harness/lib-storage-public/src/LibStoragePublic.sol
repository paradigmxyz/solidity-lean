// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library L {
    function pushPub(uint256[] storage self, uint256 v) public {
        self.push(v);
    }

    function sumPub(uint256[] storage self)
        public
        view
        returns (uint256 s)
    {
        for (uint256 i; i < self.length; i++) {
            s += self[i];
        }
    }
}

contract LibStoragePublic {
    using L for uint256[];

    uint256[] arr;

    function viaUsing(uint256 v) external {
        arr.pushPub(v);
    }

    function viaDirect(uint256 v) external {
        L.pushPub(arr, v);
    }

    function total() external view returns (uint256) {
        return arr.sumPub();
    }

    function len() external view returns (uint256) {
        return arr.length;
    }

    function elem(uint256 i) external view returns (uint256) {
        return arr[i];
    }
}
