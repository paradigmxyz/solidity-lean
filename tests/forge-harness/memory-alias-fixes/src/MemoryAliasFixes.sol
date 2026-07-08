// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MemoryAliasFixes {
    struct Bucket {
        uint256[] values;
    }

    uint256[] private stored;

    function _one(uint256 a) internal pure returns (uint256[] memory r) {
        r = new uint256[](1);
        r[0] = a;
    }

    function _two(uint256 a, uint256 b)
        internal
        pure
        returns (uint256[] memory r)
    {
        r = new uint256[](2);
        r[0] = a;
        r[1] = b;
    }

    // ---- M1: memory-ref RHS shapes alias (ternary / index / member) ----

    function ternaryDeclAlias(bool c) external pure returns (uint256, uint256) {
        uint256[] memory x = _one(1);
        uint256[] memory y = _one(2);
        uint256[] memory b = c ? x : y; // decl, ternary RHS
        b[0] = 42;
        return (x[0], b[0]); // c=true -> (42,42)
    }

    function ternaryAssignAlias(bool c)
        external
        pure
        returns (uint256, uint256)
    {
        uint256[] memory x = _one(1);
        uint256[] memory y = _one(2);
        uint256[] memory b = _one(9);
        b = c ? x : y; // assign, ternary RHS
        b[0] = 42;
        return (x[0], b[0]); // c=true -> (42,42)
    }

    function indexAssignAlias() external pure returns (uint256, uint256) {
        uint256[][] memory arr = new uint256[][](1);
        arr[0] = _one(1);
        uint256[] memory b = _one(9);
        b = arr[0]; // assign, index RHS
        b[0] = 55;
        return (arr[0][0], b[0]); // (55,55)
    }

    function memberAssignAlias() external pure returns (uint256, uint256) {
        uint256[] memory v = _one(1);
        Bucket memory s = Bucket({values: v});
        uint256[] memory b = _one(9);
        b = s.values; // assign, member RHS
        b[0] = 88;
        return (s.values[0], b[0]); // (88,88)
    }

    // ---- M2: tuple destructuring aliases each component ----

    function tupleAlias() external pure returns (uint256, uint256) {
        uint256[] memory x = _one(1);
        uint256[] memory y = _one(2);
        uint256[] memory a = _one(0);
        uint256[] memory b = _one(0);
        (a, b) = (x, y);
        a[0] = 7;
        b[0] = 9;
        return (x[0], y[0]); // (7,9)
    }

    function tupleSwap() external pure returns (uint256, uint256) {
        uint256[] memory a = _one(1);
        uint256[] memory b = _one(2);
        uint256[] memory ca = a; // external alias to a's object
        (a, b) = (b, a);
        a[0] = 99;
        return (ca[0], a[0]); // ca->old-a (1); a->old-b, a[0]=99 -> (1,99)
    }

    function tupleDecl() external pure returns (uint256, uint256) {
        uint256[] memory u = _one(1);
        (uint256[] memory a, uint256 v) = (u, 9);
        a[0] = 44;
        return (u[0], v); // (44,9)
    }

    // ---- M3: memory ref stored into aggregate element/field aliases ----

    function intoFieldAlias() external pure returns (uint256, uint256) {
        uint256[] memory v = _one(1);
        Bucket memory s = Bucket({values: v});
        uint256[] memory a = _one(5);
        s.values = a; // store ref into field
        a[0] = 77;
        return (s.values[0], a[0]); // (77,77)
    }

    function intoElementAlias() external pure returns (uint256, uint256) {
        uint256[][] memory arr = new uint256[][](1);
        arr[0] = _one(1);
        uint256[] memory a = _one(5);
        arr[0] = a; // store ref into element
        a[0] = 66;
        return (arr[0][0], a[0]); // (66,66)
    }

    // ---- Controls: value types still copy; storage<->memory independent ----

    function valueCopyControl() external pure returns (uint256, uint256) {
        uint256 x = 1;
        uint256 y = x;
        y = 7;
        return (x, y); // (1,7) source unchanged
    }

    function valueElementCopyControl()
        external
        pure
        returns (uint256, uint256)
    {
        uint256[] memory a = _one(1);
        uint256 v = 5;
        a[0] = v; // value store into element (copy)
        v = 9;
        return (a[0], v); // (5,9)
    }

    function storageToMemoryIndependence()
        external
        returns (uint256, uint256)
    {
        delete stored;
        stored.push(1);
        uint256[] memory m = stored; // deep copy
        m[0] = 100;
        return (stored[0], m[0]); // (1,100)
    }

    function memoryToStorageIndependence(uint256[] memory inp)
        external
        returns (uint256, uint256)
    {
        delete stored;
        stored = inp; // deep copy
        inp[0] = 7;
        return (stored[0], inp[0]); // (1,7) with inp[0]==1 initially
    }

    // ---- M4: abi.encode / keccak of ref-nested nested-dynamic memory ----

    function encodeBytesArray() external pure returns (uint256) {
        bytes[] memory bs = new bytes[](2);
        bs[0] = hex"0102";
        bs[1] = hex"0304";
        return keccak256(abi.encode(bs)) == keccak256(abi.encode(bs)) ? 1 : 0;
    }

    function encodeUintMatrix() external pure returns (uint256) {
        uint256[][] memory m = new uint256[][](2);
        m[0] = _two(1, 2);
        m[1] = _one(3);
        return keccak256(abi.encode(m)) == keccak256(abi.encode(m)) ? 1 : 0;
    }

    function encodeStringArray() external pure returns (uint256) {
        string[] memory ss = new string[](2);
        ss[0] = "ab";
        ss[1] = "cd";
        return keccak256(abi.encode(ss)) == keccak256(abi.encode(ss)) ? 1 : 0;
    }

    function encodeBytesArrayLength() external pure returns (uint256) {
        bytes[] memory bs = new bytes[](2);
        bs[0] = hex"0102";
        bs[1] = hex"0304";
        return abi.encode(bs).length;
    }

    function encodeUintMatrixLength() external pure returns (uint256) {
        uint256[][] memory m = new uint256[][](2);
        m[0] = _two(1, 2);
        m[1] = _one(3);
        return abi.encode(m).length;
    }
}
