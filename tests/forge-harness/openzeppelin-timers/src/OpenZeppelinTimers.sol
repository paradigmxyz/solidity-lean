// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Import-free adaptation of OpenZeppelin Contracts v4.9.6 `utils/Timers.sol`.
library OpenZeppelinTimers {
    struct Timestamp {
        uint64 _deadline;
    }

    function getDeadline(Timestamp memory timer) internal pure returns (uint64) {
        return timer._deadline;
    }

    function setDeadline(Timestamp storage timer, uint64 timestamp) internal {
        timer._deadline = timestamp;
    }

    function reset(Timestamp storage timer) internal {
        timer._deadline = 0;
    }

    function isUnset(Timestamp memory timer) internal pure returns (bool) {
        return timer._deadline == 0;
    }

    function isStarted(Timestamp memory timer) internal pure returns (bool) {
        return timer._deadline > 0;
    }

    function isPending(Timestamp memory timer) internal view returns (bool) {
        return timer._deadline > block.timestamp;
    }

    function isExpired(Timestamp memory timer) internal view returns (bool) {
        return isStarted(timer) && timer._deadline <= block.timestamp;
    }

    struct BlockNumber {
        uint64 _deadline;
    }

    function getDeadline(BlockNumber memory timer) internal pure returns (uint64) {
        return timer._deadline;
    }

    function setDeadline(BlockNumber storage timer, uint64 timestamp) internal {
        timer._deadline = timestamp;
    }

    function reset(BlockNumber storage timer) internal {
        timer._deadline = 0;
    }

    function isUnset(BlockNumber memory timer) internal pure returns (bool) {
        return timer._deadline == 0;
    }

    function isStarted(BlockNumber memory timer) internal pure returns (bool) {
        return timer._deadline > 0;
    }

    function isPending(BlockNumber memory timer) internal view returns (bool) {
        return timer._deadline > block.number;
    }

    function isExpired(BlockNumber memory timer) internal view returns (bool) {
        return isStarted(timer) && timer._deadline <= block.number;
    }
}

contract OpenZeppelinTimersHarness {
    using OpenZeppelinTimers for OpenZeppelinTimers.Timestamp;
    using OpenZeppelinTimers for OpenZeppelinTimers.BlockNumber;

    OpenZeppelinTimers.Timestamp private _timestampTimer;
    OpenZeppelinTimers.BlockNumber private _blockNumberTimer;

    event TimestampDeadlineChanged(uint64 indexed deadline);
    event BlockNumberDeadlineChanged(uint64 indexed deadline);

    function timestampDeadline() external view returns (uint64) {
        return _timestampTimer.getDeadline();
    }

    function timestampIsUnset() external view returns (bool) {
        return _timestampTimer.isUnset();
    }

    function timestampIsStarted() external view returns (bool) {
        return _timestampTimer.isStarted();
    }

    function timestampIsPending() external view returns (bool) {
        return _timestampTimer.isPending();
    }

    function timestampIsExpired() external view returns (bool) {
        return _timestampTimer.isExpired();
    }

    function blockNumberDeadline() external view returns (uint64) {
        return _blockNumberTimer.getDeadline();
    }

    function blockNumberIsUnset() external view returns (bool) {
        return _blockNumberTimer.isUnset();
    }

    function blockNumberIsStarted() external view returns (bool) {
        return _blockNumberTimer.isStarted();
    }

    function blockNumberIsPending() external view returns (bool) {
        return _blockNumberTimer.isPending();
    }

    function blockNumberIsExpired() external view returns (bool) {
        return _blockNumberTimer.isExpired();
    }

    function setTimestampDeadline(uint64 deadline)
        external
        returns (bool pending)
    {
        _timestampTimer.setDeadline(deadline);
        emit TimestampDeadlineChanged(deadline);
        return _timestampTimer.isPending();
    }

    function resetTimestampDeadline() external returns (bool unset) {
        _timestampTimer.reset();
        emit TimestampDeadlineChanged(0);
        return _timestampTimer.isUnset();
    }

    function setBlockNumberDeadline(uint64 deadline)
        external
        returns (bool pending)
    {
        _blockNumberTimer.setDeadline(deadline);
        emit BlockNumberDeadlineChanged(deadline);
        return _blockNumberTimer.isPending();
    }

    function resetBlockNumberDeadline() external returns (bool unset) {
        _blockNumberTimer.reset();
        emit BlockNumberDeadlineChanged(0);
        return _blockNumberTimer.isUnset();
    }
}
