// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Import-inlined, assembly-free adaptation of OpenZeppelin Contracts v4.9.6
// `utils/structs/DoubleEndedQueue.sol`, plus the two SafeCast helpers it uses.
library OpenZeppelinDoubleEndedQueueSafeCast {
    function toInt128(int256 value) internal pure returns (int128 downcasted) {
        downcasted = int128(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 128 bits");
    }

    function toInt256(uint256 value) internal pure returns (int256) {
        require(
            value <= uint256(type(int256).max),
            "SafeCast: value doesn't fit in an int256"
        );
        return int256(value);
    }
}

library OpenZeppelinDoubleEndedQueue {
    error Empty();
    error OutOfBounds();

    struct Bytes32Deque {
        int128 _begin;
        int128 _end;
        mapping(int128 => bytes32) _data;
    }

    function pushBack(Bytes32Deque storage deque, bytes32 value) internal {
        int128 backIndex = deque._end;
        deque._data[backIndex] = value;
        unchecked {
            deque._end = backIndex + 1;
        }
    }

    function popBack(Bytes32Deque storage deque)
        internal
        returns (bytes32 value)
    {
        if (empty(deque)) revert Empty();
        int128 backIndex;
        unchecked {
            backIndex = deque._end - 1;
        }
        value = deque._data[backIndex];
        delete deque._data[backIndex];
        deque._end = backIndex;
    }

    function pushFront(Bytes32Deque storage deque, bytes32 value) internal {
        int128 frontIndex;
        unchecked {
            frontIndex = deque._begin - 1;
        }
        deque._data[frontIndex] = value;
        deque._begin = frontIndex;
    }

    function popFront(Bytes32Deque storage deque)
        internal
        returns (bytes32 value)
    {
        if (empty(deque)) revert Empty();
        int128 frontIndex = deque._begin;
        value = deque._data[frontIndex];
        delete deque._data[frontIndex];
        unchecked {
            deque._begin = frontIndex + 1;
        }
    }

    function front(Bytes32Deque storage deque)
        internal
        view
        returns (bytes32 value)
    {
        if (empty(deque)) revert Empty();
        int128 frontIndex = deque._begin;
        return deque._data[frontIndex];
    }

    function back(Bytes32Deque storage deque)
        internal
        view
        returns (bytes32 value)
    {
        if (empty(deque)) revert Empty();
        int128 backIndex;
        unchecked {
            backIndex = deque._end - 1;
        }
        return deque._data[backIndex];
    }

    function at(Bytes32Deque storage deque, uint256 index)
        internal
        view
        returns (bytes32 value)
    {
        int256 begin = int256(deque._begin);
        int256 offset =
            OpenZeppelinDoubleEndedQueueSafeCast.toInt256(index);
        int128 idx = OpenZeppelinDoubleEndedQueueSafeCast.toInt128(
            begin + offset
        );
        if (idx >= deque._end) revert OutOfBounds();
        return deque._data[idx];
    }

    function clear(Bytes32Deque storage deque) internal {
        deque._begin = 0;
        deque._end = 0;
    }

    function length(Bytes32Deque storage deque)
        internal
        view
        returns (uint256)
    {
        unchecked {
            return uint256(int256(deque._end) - int256(deque._begin));
        }
    }

    function empty(Bytes32Deque storage deque) internal view returns (bool) {
        return deque._end <= deque._begin;
    }
}

contract OpenZeppelinDoubleEndedQueueHarness {
    using OpenZeppelinDoubleEndedQueue for
        OpenZeppelinDoubleEndedQueue.Bytes32Deque;

    OpenZeppelinDoubleEndedQueue.Bytes32Deque private _queue;

    function pushBack(bytes32 value) external returns (uint256) {
        _queue.pushBack(value);
        return _queue.length();
    }

    function pushFront(bytes32 value) external returns (uint256) {
        _queue.pushFront(value);
        return _queue.length();
    }

    function popBack() external returns (bytes32) {
        bytes32 value = _queue.popBack();
        return value;
    }

    function popFront() external returns (bytes32) {
        bytes32 value = _queue.popFront();
        return value;
    }

    function front() external view returns (bytes32) {
        return _queue.front();
    }

    function back() external view returns (bytes32) {
        return _queue.back();
    }

    function at(uint256 index) external view returns (bytes32) {
        return _queue.at(index);
    }

    function clear() external returns (uint256) {
        _queue.clear();
        return _queue.length();
    }

    function length() external view returns (uint256) {
        return _queue.length();
    }

    function empty() external view returns (bool) {
        return _queue.empty();
    }
}
