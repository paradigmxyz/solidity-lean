// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ReceiveFallbackDispatch {
    uint256 public marker;
    bytes public lastData;
    address public lastSender;
    uint256 public lastValue;

    receive() external payable {
        marker = 2;
        lastSender = msg.sender;
        lastValue = msg.value;
    }

    fallback() external payable {
        marker = 1;
        lastData = msg.data;
        lastSender = msg.sender;
        lastValue = msg.value;
    }

    function touch(uint256 value) external payable returns (uint256) {
        marker = value;
        lastSender = msg.sender;
        lastValue = msg.value;
        return value + 1;
    }

    function snapshot()
        external
        view
        returns (
            uint256 currentMarker,
            address sender,
            uint256 value,
            uint256 dataLength
        )
    {
        return (marker, lastSender, lastValue, lastData.length);
    }
}

contract ReceiveFallbackBytes {
    fallback(bytes calldata input)
        external
        payable
        returns (bytes memory output)
    {
        return input;
    }
}

contract ReceiveFallbackOnlyFallback {
    uint256 public marker;

    fallback() external payable {
        marker = 3;
    }
}

contract ReceiveFallbackOnlyReceive {
    uint256 public marker;

    receive() external payable {
        marker = 4;
    }
}

contract ReceiveFallbackMissing {
    function touch() external {}
}

contract ReceiveFallbackBase {
    uint256 public marker;

    receive() external payable virtual {
        marker = 5;
    }

    fallback() external payable virtual {
        marker = 6;
    }
}

contract ReceiveFallbackChild is ReceiveFallbackBase {}

contract ReceiveFallbackOverride is ReceiveFallbackBase {
    receive() external payable override {
        marker = 7;
    }

    fallback() external payable override {
        marker = 8;
    }
}
