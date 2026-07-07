// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract DeleteAgg {
    struct S { uint256 a; uint256[] arr; uint256 b; }
    S s;
    uint256[] xs;
    mapping(uint256 => uint256) m;

    function setup() external {
        s.a = 111;
        s.arr.push(1); s.arr.push(2); s.arr.push(3);
        s.b = 222;
        xs.push(10); xs.push(20); xs.push(30);
        m[5] = 500;
    }
    function delStruct() external { delete s; }          // deletes a with dynamic-array field
    function delArrElem() external { delete xs[1]; }      // zero one element
    function popArr() external { xs.pop(); }
    function delMapKey() external { delete m[5]; }

    function getSA() external view returns (uint256) { return s.a; }
    function getSB() external view returns (uint256) { return s.b; }
    function getSArrLen() external view returns (uint256) { return s.arr.length; }
    function getXs(uint256 i) external view returns (uint256) { return xs[i]; }
    function getXsLen() external view returns (uint256) { return xs.length; }
    function getM(uint256 k) external view returns (uint256) { return m[k]; }
}
