// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// ADDRESS-NESTED-CONVERSION (#181): a chain of >= 3 consecutive non-payable
// `address(...)` conversions whose innermost argument is a CONSTANT literal is
// accepted by solc and behaves as the identity on the folded address value, so
// `address(address(address(0x1234)))` = `address(0x1234)` = 0x1234 (= 4660).
// solidity-lean accepted the contract at typecheck but FAILED TO LOWER the
// nested chain (`Expr.toCore?` bailed with `none` in the nonpayable-`address`
// arm because the inner `address(0x1234)` was an `isAddressLiteralCandidate`),
// which poisoned the WHOLE contract (every function, even unrelated ones, then
// failed with TypeError.unsupported). The fix recurses into a nested conversion
// argument instead of bailing, lowering the inner cast; a genuine out-of-range
// bare literal stays rejected. depth-2 already worked (folded a bare literal),
// as did a depth-3 chain over a PARAMETER (recursion path).
contract AddressNestedConvTarget {
    // depth-3 literal chain -> 0x1234.
    function d3() external pure returns (address) {
        return address(address(address(0x1234)));
    }
    // depth-4 literal chain -> 0x1234.
    function d4() external pure returns (address) {
        return address(address(address(address(0x1234))));
    }
    // payable sibling of the depth-3 chain -> 0x1234.
    function p3() external pure returns (address payable) {
        return payable(address(address(address(0x1234))));
    }
    // depth-2 chain must STILL work -> 0x1234.
    function d2() external pure returns (address) {
        return address(address(0x1234));
    }
    // Unrelated function: must lower (contract no longer poisoned) -> 7.
    function h() external pure returns (uint256) {
        return 7;
    }
}
