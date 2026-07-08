// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Other {
    function ping() external pure returns (uint256) {
        return 7;
    }
}

// A contract-typed local (`Other o`) is an address-carrying value (160-bit).
// It can be declared from an address, cast back to address, and used wherever
// an address is expected.
contract ContractTypedLocals {
    // literal address -> contract -> address, value preserved
    function addrOfContract() external pure returns (uint160) {
        Other o = Other(address(uint160(0x1234567890abcdef1234)));
        return uint160(address(o));
    }
    // address -> contract -> address round trip
    function roundTrip(address a) external pure returns (address) {
        Other o = Other(a);
        return address(o);
    }
    // contract-typed local passed where an address argument is expected
    function passAsAddress(address a) external pure returns (uint160) {
        Other o = Other(a);
        return asUint160(address(o));
    }
    // the contract-typed local's underlying address queried for its balance
    function balanceOfLocal(address a) external view returns (uint256) {
        Other o = Other(a);
        return address(o).balance;
    }

    function asUint160(address a) internal pure returns (uint160) {
        return uint160(a);
    }
}
