// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Import-inlined adaptation of OpenZeppelin Contracts v4.9.6
// `utils/Counters.sol`.
library OpenZeppelinCounters {
    struct Counter {
        uint256 _value;
    }

    function current(Counter storage counter) internal view returns (uint256) {
        return counter._value;
    }

    function increment(Counter storage counter) internal {
        unchecked {
            counter._value += 1;
        }
    }

    function decrement(Counter storage counter) internal {
        uint256 value = counter._value;
        require(value > 0, "Counter: decrement overflow");
        unchecked {
            counter._value = value - 1;
        }
    }

    function reset(Counter storage counter) internal {
        counter._value = 0;
    }
}

contract OpenZeppelinCountersHarness {
    using OpenZeppelinCounters for OpenZeppelinCounters.Counter;

    OpenZeppelinCounters.Counter private _ids;
    OpenZeppelinCounters.Counter private _other;

    event Counted(uint256 value);

    function current() external view returns (uint256) {
        return _ids.current();
    }

    function other() external view returns (uint256) {
        return _other.current();
    }

    function increment() external returns (uint256) {
        _ids.increment();
        uint256 value = _ids.current();
        emit Counted(value);
        return value;
    }

    function incrementByTwo() external returns (uint256) {
        _ids.increment();
        _ids.increment();
        return _ids.current();
    }

    function decrement() external returns (uint256) {
        _ids.decrement();
        return _ids.current();
    }

    function reset() external {
        _ids.reset();
    }

    function incrementOther() external returns (uint256) {
        _other.increment();
        return _other.current();
    }

    function decrementOther() external returns (uint256) {
        _other.decrement();
        return _other.current();
    }
}
