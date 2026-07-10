// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library L2 {
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

contract LibStoragePublic2 {
    using L2 for uint256[];

    struct S {
        uint256[] a;
    }

    mapping(uint256 => uint256[]) m; // slot 0
    S s; // slot 1
    uint256[][] aa; // slot 2

    // Storage-pointer argument = a MAPPING VALUE `m[k]` (runtime keccak slot),
    // passed directly to the public library.
    function pushMapping(uint256 k, uint256 v) external {
        L2.pushPub(m[k], v);
    }

    // Storage-pointer argument = a STRUCT-MEMBER array `s.a` (compile-time
    // additive slot), via the using-for receiver form.
    function pushStruct(uint256 v) external {
        s.a.pushPub(v);
    }

    // Storage-pointer argument = a `T storage` LOCAL bound to a nested-array
    // element `aa[i]` (runtime keccak slot), passed directly.
    function pushLocal(uint256 i, uint256 v) external {
        uint256[] storage p = aa[i];
        L2.pushPub(p, v);
    }

    function addRow() external {
        aa.push();
    }

    // Read-backs (real-EVM ground truth in Forge).
    function mapLen(uint256 k) external view returns (uint256) {
        return m[k].length;
    }

    function mapElem(uint256 k, uint256 i) external view returns (uint256) {
        return m[k][i];
    }

    function mapSum(uint256 k) external view returns (uint256) {
        return m[k].sumPub();
    }

    function structLen() external view returns (uint256) {
        return s.a.length;
    }

    function structElem(uint256 i) external view returns (uint256) {
        return s.a[i];
    }

    function aaLen(uint256 i) external view returns (uint256) {
        return aa[i].length;
    }

    function aaElem(uint256 i, uint256 j) external view returns (uint256) {
        return aa[i][j];
    }
}
