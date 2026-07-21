pragma solidity ^0.8.0;
struct S { uint256 a; }
library Lib { function a(S memory s) internal pure returns (uint256) { return 7; } }
contract T {
    using Lib for S;
    S internal st;
    function g() public view returns (uint256) {
        return st.a;
    }
}
