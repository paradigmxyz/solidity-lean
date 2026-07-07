// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Other {
    function ping() external pure returns (uint256) { return 1; }
}

contract ContractConv {
    // contract -> address -> uint160 preserves the address value
    function addrOfContract() external pure returns (uint160) {
        Other o = Other(address(uint160(0x1234567890abcdef1234)));
        return uint160(address(o));
    }
    // address -> contract -> address round trip
    function roundTrip() external pure returns (uint160) {
        address a = address(uint160(0xdeadbeef00112233));
        Other o = Other(a);
        return uint160(address(o));
    }
}
