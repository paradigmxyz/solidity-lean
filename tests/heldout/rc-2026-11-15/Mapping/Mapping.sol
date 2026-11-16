// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

contract Mapping {
    // Mapping from address to uint
    mapping(address => uint256) public myMap;

    /// @custom:succeeds-if msg.value == 0
    /// @custom:ensures result == myMap[_addr]
    function get(address _addr) public view returns (uint256) {
        // Mapping always returns a value.
        // If the value was never set, it will return the default value.
        return myMap[_addr];
    }

    /// @custom:succeeds-if msg.value == 0
    /// @custom:ensures myMap[_addr] == _i
    function set(address _addr, uint256 _i) public {
        // Update the value at this address
        myMap[_addr] = _i;
    }

    /// @custom:succeeds-if msg.value == 0
    /// @custom:ensures myMap[_addr] == 0
    function remove(address _addr) public {
        // Reset the value to the default value.
        delete myMap[_addr];
    }
}
