// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// ABI-DECODE-ADDRESS-PAYABLE — solc forces every top-level decoded `address`
// component of `abi.decode`'s result type to `address payable`
// (`TypeChecker.cpp:150-152`, `typeCheckABIDecodeAndRetrieveReturnType`):
//
//     // We force address payable for address types.
//     if (actualType->category() == Type::Category::Address)
//         actualType = TypeProvider::payableAddress();
//
// so `abi.decode(data, (address))` yields an `address payable`, assignable to an
// `address payable` variable and carrying the payable-only `.send`/`.transfer`
// members. solidity-lean formerly returned plain `address` and over-rejected
// the whole contract at lowering/typecheck.
contract AbiDecodeAddressPayableHarnessTarget {
    // Decoded address assigned to an `address payable` variable, then returned.
    // Formerly over-rejected because a plain `address` is not assignable to
    // `address payable`.
    function payableRoundtrip() external pure returns (address) {
        bytes memory data = abi.encode(address(uint160(0x1234)));
        address payable p = abi.decode(data, (address));
        return p; // 0x1234
    }

    // `.send` — a payable-only member — called directly on the decoded address.
    // A zero-value send to a code-less address succeeds and returns true.
    function sendToDecoded() external returns (bool) {
        bytes memory data = abi.encode(address(uint160(0x5678)));
        return abi.decode(data, (address)).send(0); // true
    }
}
