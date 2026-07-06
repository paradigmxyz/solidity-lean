// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Import-free adaptation of OpenZeppelin Contracts v5.6.1
// `utils/types/Time.sol`, with the needed Math.max and SafeCast.toUint48
// helpers inlined to keep import resolution out of scope.
library OpenZeppelinTimeMath {
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a > b ? a : b;
    }
}

library OpenZeppelinTimeSafeCast {
    error SafeCastOverflowedUintDowncast(uint8 bits, uint256 value);

    function toUint48(uint256 value) internal pure returns (uint48) {
        if (value > type(uint48).max) {
            revert SafeCastOverflowedUintDowncast(48, value);
        }
        return uint48(value);
    }
}

library OpenZeppelinTime {
    using OpenZeppelinTime for *;

    function timestamp() internal view returns (uint48) {
        return OpenZeppelinTimeSafeCast.toUint48(block.timestamp);
    }

    function blockNumber() internal view returns (uint48) {
        return OpenZeppelinTimeSafeCast.toUint48(block.number);
    }

    type Delay is uint112;

    function toDelay(uint32 duration) internal pure returns (Delay) {
        return Delay.wrap(duration);
    }

    function _getFullAt(Delay self, uint48 timepoint)
        private
        pure
        returns (uint32 valueBefore, uint32 valueAfter, uint48 effect)
    {
        (valueBefore, valueAfter, effect) = self.unpack();
        return
            effect <= timepoint
                ? (valueAfter, 0, 0)
                : (valueBefore, valueAfter, effect);
    }

    function getFull(Delay self)
        internal
        view
        returns (uint32 valueBefore, uint32 valueAfter, uint48 effect)
    {
        return _getFullAt(self, timestamp());
    }

    function get(Delay self) internal view returns (uint32) {
        (uint32 delay, , ) = self.getFull();
        return delay;
    }

    function withUpdate(Delay self, uint32 newValue, uint32 minSetback)
        internal
        view
        returns (Delay updatedDelay, uint48 effect)
    {
        uint32 value = self.get();
        uint32 setback = uint32(
            OpenZeppelinTimeMath.max(
                minSetback,
                value > newValue ? value - newValue : 0
            )
        );
        effect = timestamp() + setback;
        return (pack(value, newValue, effect), effect);
    }

    function unpack(Delay self)
        internal
        pure
        returns (uint32 valueBefore, uint32 valueAfter, uint48 effect)
    {
        uint112 raw = Delay.unwrap(self);

        valueAfter = uint32(raw);
        valueBefore = uint32(raw >> 32);
        effect = uint48(raw >> 64);

        return (valueBefore, valueAfter, effect);
    }

    function pack(uint32 valueBefore, uint32 valueAfter, uint48 effect)
        internal
        pure
        returns (Delay)
    {
        return
            Delay.wrap(
                (uint112(effect) << 64) |
                    (uint112(valueBefore) << 32) |
                    uint112(valueAfter)
            );
    }
}

contract OpenZeppelinTimeHarness {
    using OpenZeppelinTime for OpenZeppelinTime.Delay;

    OpenZeppelinTime.Delay private _delay;

    event DelayStored(uint32 indexed current);
    event DelayScheduled(
        uint32 indexed valueBefore,
        uint32 indexed valueAfter,
        uint48 effect
    );

    function timestampNow() external view returns (uint48) {
        return OpenZeppelinTime.timestamp();
    }

    function blockNumberNow() external view returns (uint48) {
        return OpenZeppelinTime.blockNumber();
    }

    function store(uint32 duration) external returns (uint32 currentValue) {
        _delay = OpenZeppelinTime.toDelay(duration);
        currentValue = _delay.get();
        emit DelayStored(currentValue);
    }

    function current() external view returns (uint32) {
        return _delay.get();
    }

    function full()
        external
        view
        returns (uint32 valueBefore, uint32 valueAfter, uint48 effect)
    {
        return _delay.getFull();
    }

    function unpackStored()
        external
        view
        returns (uint32 valueBefore, uint32 valueAfter, uint48 effect)
    {
        return _delay.unpack();
    }

    function packUnpack(
        uint32 valueBefore,
        uint32 valueAfter,
        uint48 effect
    )
        external
        pure
        returns (
            uint32 unpackedBefore,
            uint32 unpackedAfter,
            uint48 unpackedEffect
        )
    {
        OpenZeppelinTime.Delay packed =
            OpenZeppelinTime.pack(valueBefore, valueAfter, effect);
        (unpackedBefore, unpackedAfter, unpackedEffect) = packed.unpack();
    }

    function schedule(uint32 newValue, uint32 minSetback)
        external
        returns (
            uint32 valueBefore,
            uint32 valueAfter,
            uint48 effect,
            uint32 currentValue
        )
    {
        (_delay, effect) = _delay.withUpdate(newValue, minSetback);
        (valueBefore, valueAfter, effect) = _delay.unpack();
        currentValue = _delay.get();
        emit DelayScheduled(valueBefore, valueAfter, effect);
    }
}
