// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract Order {
    uint256 public log;
    function a() internal returns (uint256) { log = log*10 + 1; return 1; }
    function b() internal returns (uint256) { log = log*10 + 2; return 2; }
    // solc evaluates arguments; observe order via log. Return log after a()+b() style call.
    function argOrder() external returns (uint256) { uint256 s = a() + b(); return log*1000 + s; }
    // index/value order: arr[i()] = v()
    uint256[3] arr;
    function idxA() internal returns (uint256) { log = log*10 + 7; return 0; }
    function valB() internal returns (uint256) { log = log*10 + 8; return 5; }
    function assignOrder() external returns (uint256) { arr[idxA()] = valB(); return log; }
}
