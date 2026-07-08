// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// G18 pin (docs/solidus-solc-deep-comparison.md): a `try extCall() returns (...)`
// whose bound return value is an EXTERNAL FUNCTION-typed value. Pin that the
// external function pointer round-trips through the try binding: the caller
// binds it and then invokes it, observing the callee's result.
interface IProvider {
    // Returns an external function pointer (address ++ selector, 24 bytes).
    function getCb()
        external
        view
        returns (function() external view returns (uint256));

    // The callback target the returned pointer points at.
    function value() external view returns (uint256);
}

contract TryExternalFnReturnHarnessTarget {
    // try-binds the external-function-typed return, then invokes it.
    function tryGetAndCall(IProvider p) external view returns (uint256) {
        try p.getCb() returns (function() external view returns (uint256) cb) {
            return cb();
        } catch {
            return 0;
        }
    }
}

// A concrete provider so the Forge ground truth exercises real EVM ABI
// encode/decode of an external function pointer across the try boundary.
contract Provider is IProvider {
    function value() external pure override returns (uint256) {
        return 42;
    }

    function getCb()
        external
        view
        override
        returns (function() external view returns (uint256))
    {
        return this.value;
    }
}
