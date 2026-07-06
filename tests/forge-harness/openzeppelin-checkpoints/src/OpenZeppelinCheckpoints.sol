// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

// Import-inlined, assembly-free adaptation of the Trace256 path from
// OpenZeppelin Contracts v5.6.1 `utils/structs/Checkpoints.sol`.
library OpenZeppelinCheckpointsMath {
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        unchecked {
            return (a & b) + (a ^ b) / 2;
        }
    }
}

library OpenZeppelinCheckpoints {
    error CheckpointUnorderedInsertion();

    struct Trace256 {
        Checkpoint256[] _checkpoints;
    }

    struct Checkpoint256 {
        uint256 _key;
        uint256 _value;
    }

    function push(Trace256 storage self, uint256 key, uint256 value)
        internal
        returns (uint256 oldValue, uint256 newValue)
    {
        return _insert(self._checkpoints, key, value);
    }

    function lowerLookup(Trace256 storage self, uint256 key)
        internal
        view
        returns (uint256)
    {
        uint256 len = self._checkpoints.length;
        uint256 pos = _lowerBinaryLookup(self._checkpoints, key, 0, len);
        return pos == len ? 0 : self._checkpoints[pos]._value;
    }

    function upperLookup(Trace256 storage self, uint256 key)
        internal
        view
        returns (uint256)
    {
        uint256 len = self._checkpoints.length;
        uint256 pos = _upperBinaryLookup(self._checkpoints, key, 0, len);
        return pos == 0 ? 0 : self._checkpoints[pos - 1]._value;
    }

    function upperLookupRecent(Trace256 storage self, uint256 key)
        internal
        view
        returns (uint256)
    {
        return upperLookup(self, key);
    }

    function latest(Trace256 storage self) internal view returns (uint256) {
        uint256 pos = self._checkpoints.length;
        return pos == 0 ? 0 : self._checkpoints[pos - 1]._value;
    }

    function latestCheckpoint(Trace256 storage self)
        internal
        view
        returns (bool exists, uint256 _key, uint256 _value)
    {
        uint256 pos = self._checkpoints.length;
        if (pos == 0) {
            return (false, 0, 0);
        } else {
            Checkpoint256 storage ckpt = self._checkpoints[pos - 1];
            return (true, ckpt._key, ckpt._value);
        }
    }

    function length(Trace256 storage self) internal view returns (uint256) {
        return self._checkpoints.length;
    }

    function at(Trace256 storage self, uint32 pos)
        internal
        view
        returns (Checkpoint256 memory)
    {
        return self._checkpoints[pos];
    }

    function _insert(
        Checkpoint256[] storage self,
        uint256 key,
        uint256 value
    ) private returns (uint256 oldValue, uint256 newValue) {
        uint256 pos = self.length;

        if (pos > 0) {
            Checkpoint256 storage last = self[pos - 1];
            uint256 lastKey = last._key;
            uint256 lastValue = last._value;

            if (lastKey > key) {
                revert CheckpointUnorderedInsertion();
            }

            if (lastKey == key) {
                last._value = value;
            } else {
                _pushNew(self, key, value);
            }

            return (lastValue, value);
        } else {
            _pushNew(self, key, value);
            return (0, value);
        }
    }

    function _pushNew(
        Checkpoint256[] storage self,
        uint256 key,
        uint256 value
    ) private {
        self.push();
        Checkpoint256 storage checkpoint = self[self.length - 1];
        checkpoint._key = key;
        checkpoint._value = value;
    }

    function _upperBinaryLookup(
        Checkpoint256[] storage self,
        uint256 key,
        uint256 low,
        uint256 high
    ) private view returns (uint256) {
        while (low < high) {
            uint256 mid = OpenZeppelinCheckpointsMath.average(low, high);
            if (self[mid]._key > key) {
                high = mid;
            } else {
                low = mid + 1;
            }
        }
        return high;
    }

    function _lowerBinaryLookup(
        Checkpoint256[] storage self,
        uint256 key,
        uint256 low,
        uint256 high
    ) private view returns (uint256) {
        while (low < high) {
            uint256 mid = OpenZeppelinCheckpointsMath.average(low, high);
            if (self[mid]._key < key) {
                low = mid + 1;
            } else {
                high = mid;
            }
        }
        return high;
    }
}

contract OpenZeppelinCheckpointsHarness {
    using OpenZeppelinCheckpoints for OpenZeppelinCheckpoints.Trace256;

    error CheckpointUnorderedInsertion();

    OpenZeppelinCheckpoints.Trace256 private _trace;

    function push(uint256 key, uint256 value)
        external
        returns (uint256 oldValue, uint256 newValue)
    {
        uint256 pos = _trace._checkpoints.length;

        if (pos > 0) {
            OpenZeppelinCheckpoints.Checkpoint256 storage last =
                _trace._checkpoints[pos - 1];
            uint256 lastKey = last._key;
            uint256 lastValue = last._value;

            if (lastKey > key) {
                revert CheckpointUnorderedInsertion();
            }

            if (lastKey == key) {
                last._value = value;
            } else {
                _trace._checkpoints.push();
                OpenZeppelinCheckpoints.Checkpoint256 storage checkpoint =
                    _trace._checkpoints[_trace._checkpoints.length - 1];
                checkpoint._key = key;
                checkpoint._value = value;
            }

            return (lastValue, value);
        } else {
            _trace._checkpoints.push();
            OpenZeppelinCheckpoints.Checkpoint256 storage checkpoint =
                _trace._checkpoints[_trace._checkpoints.length - 1];
            checkpoint._key = key;
            checkpoint._value = value;
            return (0, value);
        }
    }

    function pushThree(
        uint256 firstKey,
        uint256 firstValue,
        uint256 secondKey,
        uint256 secondValue,
        uint256 thirdKey,
        uint256 thirdValue
    ) external returns (uint256) {
        _trace._checkpoints.push();
        OpenZeppelinCheckpoints.Checkpoint256 storage checkpoint =
            _trace._checkpoints[_trace._checkpoints.length - 1];
        checkpoint._key = firstKey;
        checkpoint._value = firstValue;

        _trace._checkpoints.push();
        OpenZeppelinCheckpoints.Checkpoint256 storage second =
            _trace._checkpoints[_trace._checkpoints.length - 1];
        second._key = secondKey;
        second._value = secondValue;

        _trace._checkpoints.push();
        OpenZeppelinCheckpoints.Checkpoint256 storage third =
            _trace._checkpoints[_trace._checkpoints.length - 1];
        third._key = thirdKey;
        third._value = thirdValue;

        return _trace.length();
    }

    function lowerLookup(uint256 key) external view returns (uint256) {
        return _trace.lowerLookup(key);
    }

    function upperLookup(uint256 key) external view returns (uint256) {
        return _trace.upperLookup(key);
    }

    function upperLookupRecent(uint256 key) external view returns (uint256) {
        return _trace.upperLookupRecent(key);
    }

    function latest() external view returns (uint256) {
        return _trace.latest();
    }

    function latestCheckpoint()
        external
        view
        returns (bool exists, uint256 key, uint256 value)
    {
        return _trace.latestCheckpoint();
    }

    function length() external view returns (uint256) {
        return _trace.length();
    }

    function keyAt(uint32 pos) external view returns (uint256) {
        OpenZeppelinCheckpoints.Checkpoint256 memory checkpoint =
            _trace.at(pos);
        return checkpoint._key;
    }

    function valueAt(uint32 pos) external view returns (uint256) {
        OpenZeppelinCheckpoints.Checkpoint256 memory checkpoint =
            _trace.at(pos);
        return checkpoint._value;
    }
}
