// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;
// Over-accept guard: WIDER receiver. `using L for uint256` + `f(uint8 self)`,
// receiver is uint256. uint256 is NOT implicitly convertible to uint8, so the
// member is not attached — solc REJECTS.
library L { function f(uint8 self) internal pure returns (uint8) { return self + 1; } }
contract C {
    using L for uint256;
    function g(uint256 x) external pure returns (uint8) { return x.f(); }
}
