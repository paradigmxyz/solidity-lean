// SPDX-License-Identifier: BSD-3-Clause
pragma solidity ^0.8.20;

import {CompoundTimelock, CompoundTimelockTarget} from "../src/CompoundTimelock.sol";

interface Vm {
    function warp(uint256) external;
    function prank(address) external;
    function deal(address, uint256) external;
}

contract CompoundTimelockForgeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    receive() external payable {}

    function _call(address target, bytes memory payload)
        private
        returns (bool ok, bytes memory result)
    {
        (ok, result) = target.call(payload);
    }

    function testConstructorConstantsAndAdmin() public {
        CompoundTimelock timelock =
            new CompoundTimelock(address(this), 3 days);

        require(timelock.GRACE_PERIOD() == 14 days, "grace");
        require(timelock.MINIMUM_DELAY() == 2 days, "min");
        require(timelock.MAXIMUM_DELAY() == 30 days, "max");
        require(timelock.admin() == address(this), "admin");
        require(timelock.delay() == 3 days, "delay");

        (bool tooShort, ) = _call(
            address(timelock),
            abi.encodeWithSelector(timelock.setDelay.selector, 1 days)
        );
        require(!tooShort, "setDelay self only");
    }

    function testQueueAndCancelTransaction() public {
        CompoundTimelock timelock =
            new CompoundTimelock(address(this), 2 days);
        CompoundTimelockTarget target = new CompoundTimelockTarget();
        uint256 eta = block.timestamp + timelock.delay();
        bytes memory data = abi.encode(uint256(33));

        bytes32 txHash = timelock.queueTransaction(
            address(target),
            0,
            "setValue(uint256)",
            data,
            eta
        );
        require(timelock.queuedTransactions(txHash), "queued");

        timelock.cancelTransaction(
            address(target),
            0,
            "setValue(uint256)",
            data,
            eta
        );
        require(!timelock.queuedTransactions(txHash), "cancelled");
    }

    function testQueueRejectsSenderAndEta() public {
        CompoundTimelock timelock =
            new CompoundTimelock(address(this), 2 days);
        CompoundTimelockTarget target = new CompoundTimelockTarget();
        bytes memory data = abi.encode(uint256(33));

        (bool etaOk, ) = _call(
            address(timelock),
            abi.encodeWithSelector(
                timelock.queueTransaction.selector,
                address(target),
                0,
                "setValue(uint256)",
                data,
                block.timestamp + 1 days
            )
        );
        require(!etaOk, "eta rejected");

        vm.prank(address(0xbeef));
        (bool senderOk, ) = _call(
            address(timelock),
            abi.encodeWithSelector(
                timelock.queueTransaction.selector,
                address(target),
                0,
                "setValue(uint256)",
                data,
                block.timestamp + 2 days
            )
        );
        require(!senderOk, "sender rejected");
    }

    function testExecuteTransactionWithSignature() public {
        CompoundTimelock timelock =
            new CompoundTimelock(address(this), 2 days);
        CompoundTimelockTarget target = new CompoundTimelockTarget();
        vm.deal(address(timelock), 10);

        uint256 eta = block.timestamp + timelock.delay();
        bytes memory data = abi.encode(uint256(33));
        bytes32 txHash = timelock.queueTransaction(
            address(target),
            5,
            "setValue(uint256)",
            data,
            eta
        );

        vm.warp(eta);
        bytes memory result = timelock.executeTransaction(
            address(target),
            5,
            "setValue(uint256)",
            data,
            eta
        );

        require(!timelock.queuedTransactions(txHash), "cleared");
        require(target.value() == 33, "target value");
        require(target.lastValue() == 5, "target eth");
        require(abi.decode(result, (uint256)) == 38, "return data");
    }

    function testExecuteTransactionWithRawDataAndStaleGuard() public {
        CompoundTimelock timelock =
            new CompoundTimelock(address(this), 2 days);
        CompoundTimelockTarget target = new CompoundTimelockTarget();

        uint256 eta = block.timestamp + timelock.delay();
        bytes memory rawData =
            abi.encodeWithSelector(target.bump.selector, uint256(7));
        bytes32 txHash = timelock.queueTransaction(
            address(target),
            0,
            "",
            rawData,
            eta
        );

        (bool early, ) = _call(
            address(timelock),
            abi.encodeWithSelector(
                timelock.executeTransaction.selector,
                address(target),
                0,
                "",
                rawData,
                eta
            )
        );
        require(!early, "early rejected");
        require(timelock.queuedTransactions(txHash), "still queued");

        vm.warp(eta + timelock.GRACE_PERIOD() + 1);
        (bool stale, ) = _call(
            address(timelock),
            abi.encodeWithSelector(
                timelock.executeTransaction.selector,
                address(target),
                0,
                "",
                rawData,
                eta
            )
        );
        require(!stale, "stale rejected");
        require(timelock.queuedTransactions(txHash), "stale kept");
    }
}
