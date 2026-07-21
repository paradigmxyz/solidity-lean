pragma solidity ^0.8.0;
struct S { uint256 a; }
library Lib { function a(S memory s) internal pure returns (uint256) { return s.a; } }
contract T {
    using Lib for S;
    function g() public pure returns (uint256) {
        S memory s = S(5);
        return s.a;
    }
}
