// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

contract BaseQualifiedFunctionStateVariableTarget {
    function() returns (uint256) internal x;

    function g() public pure returns (uint256) {}

    function h() public returns (uint256) {
        return BaseQualifiedFunctionStateVariableTarget.x();
    }
}

contract QualifiedBase {
    function f() internal pure returns (uint256) {
        return 7;
    }
}

contract QualifiedDerived is QualifiedBase {
    function alt() internal pure returns (uint256) {
        return 2;
    }

    function shadowed() public pure returns (uint256) {
        function() internal pure returns (uint256) f = alt;
        f;
        return QualifiedBase.f();
    }
}
