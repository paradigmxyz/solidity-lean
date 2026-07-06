// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Import-inlined, assembly-free adaptation of OpenZeppelin Contracts v5.6.1
// ERC2771Context and Context. The source-level semantics remain the upstream
// calldata suffix rules; import resolution is intentionally outside this layer.
abstract contract OpenZeppelinERC2771ContextBase {
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

abstract contract OpenZeppelinERC2771Context is OpenZeppelinERC2771ContextBase {
    address private immutable _trustedForwarder;

    constructor(address trustedForwarder_) {
        _trustedForwarder = trustedForwarder_;
    }

    function trustedForwarder() public view virtual returns (address) {
        return _trustedForwarder;
    }

    function isTrustedForwarder(address forwarder)
        public
        view
        virtual
        returns (bool)
    {
        return forwarder == trustedForwarder();
    }

    function _msgSender()
        internal
        view
        virtual
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
        virtual
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
        virtual
        override
        returns (uint256)
    {
        return 20;
    }
}

contract OpenZeppelinERC2771ContextHarness is OpenZeppelinERC2771Context {
    constructor(address trustedForwarder_)
        OpenZeppelinERC2771Context(trustedForwarder_)
    {}

    function exposedSender() external view returns (address) {
        return _msgSender();
    }

    function exposedData() external view returns (bytes memory) {
        return _msgData();
    }

    function exposedSenderDataAndPayloadLength(bytes calldata payload)
        external
        view
        returns (address, bytes memory, uint256)
    {
        bytes calldata data = _msgData();
        return (_msgSender(), data, payload.length);
    }

    function exposedContextSuffixLength() external view returns (uint256) {
        return _contextSuffixLength();
    }
}
