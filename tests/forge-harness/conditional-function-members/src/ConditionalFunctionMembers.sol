// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

contract ConditionalFunctionMembers {
    function f() public {}
    function g() public {}
    function selectorMatches(bool choose) external view returns (bool) {
        bytes4 expected = choose ? bytes4(0x26121ff0) : bytes4(0xe2179b8e);
        return (choose ? this.f : this.g).selector == expected;
    }
    function namedSelectorPure() external pure returns (bool) {
        return this.f.selector == bytes4(0x26121ff0);
    }
}
