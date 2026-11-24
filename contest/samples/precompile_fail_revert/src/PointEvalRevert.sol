// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Control for precompile_fail_oog: one failing point-evaluation staticcall
// returns false with empty returndata and burns its forwarded gas, but the
// frame still has gas left and reverts at source level.
contract PointEvalRevert {
    error Failed(bool ok, uint256 len);

    function f() external view returns (uint256) {
        (bool ok, bytes memory ret) = address(10).staticcall(abi.encode(bytes32(0), bytes32(0)));
        if (!ok) revert Failed(ok, ret.length);
        return 1;
    }
}
