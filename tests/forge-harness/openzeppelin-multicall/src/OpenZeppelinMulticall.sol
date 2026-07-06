// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Import-inlined, assembly-free adaptation of OpenZeppelin Contracts v5.6.1
// Multicall, Address.functionDelegateCall, and Context. Import resolution and
// byte-level revert bubbling are intentionally outside this source layer.
abstract contract OpenZeppelinMulticallContext {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }
}

library OpenZeppelinMulticallAddress {
    function functionDelegateCall(address target, bytes memory data)
        internal
        returns (bytes memory)
    {
        (bool success, bytes memory returndata) = target.delegatecall(data);
        require(success, "Address: low-level delegate call failed");
        return returndata;
    }
}

abstract contract OpenZeppelinMulticall is OpenZeppelinMulticallContext {
    function multicall(bytes[] calldata data)
        public
        virtual
        returns (bytes[] memory results)
    {
        bytes memory context = msg.sender == _msgSender()
            ? new bytes(0)
            : msg.data[msg.data.length - _contextSuffixLength():];

        results = new bytes[](data.length);
        for (uint256 i = 0; i < data.length; i++) {
            results[i] = OpenZeppelinMulticallAddress.functionDelegateCall(
                address(this),
                bytes.concat(data[i], context)
            );
        }
        return results;
    }
}

contract OpenZeppelinMulticallHarness is OpenZeppelinMulticall {
    address private immutable _trustedForwarder;
    uint256 public value;

    constructor(address trustedForwarder_) {
        _trustedForwarder = trustedForwarder_;
    }

    function trustedForwarder() public view returns (address) {
        return _trustedForwarder;
    }

    function isTrustedForwarder(address forwarder)
        public
        view
        returns (bool)
    {
        return forwarder == trustedForwarder();
    }

    function _msgSender()
        internal
        view
        override
        returns (address)
    {
        uint256 calldataLength = msg.data.length;
        uint256 contextSuffixLength = _contextSuffixLength();
        if (
            calldataLength >= contextSuffixLength &&
            isTrustedForwarder(msg.sender)
        ) {
            unchecked {
                return address(
                    bytes20(msg.data[calldataLength - contextSuffixLength:])
                );
            }
        } else {
            return super._msgSender();
        }
    }

    function _msgData()
        internal
        view
        override
        returns (bytes calldata)
    {
        uint256 calldataLength = msg.data.length;
        uint256 contextSuffixLength = _contextSuffixLength();
        if (
            calldataLength >= contextSuffixLength &&
            isTrustedForwarder(msg.sender)
        ) {
            unchecked {
                return msg.data[:calldataLength - contextSuffixLength];
            }
        } else {
            return super._msgData();
        }
    }

    function _contextSuffixLength()
        internal
        view
        override
        returns (uint256)
    {
        return 20;
    }

    function setValue(uint256 next) external returns (uint256) {
        value = next;
        return next + 1;
    }

    function addValue(uint256 delta) external returns (uint256) {
        value += delta;
        return value;
    }

    function exposedSenderDataLength()
        external
        view
        returns (address, uint256)
    {
        return (_msgSender(), _msgData().length);
    }

    function fail() external pure {
        revert("inner");
    }
}
