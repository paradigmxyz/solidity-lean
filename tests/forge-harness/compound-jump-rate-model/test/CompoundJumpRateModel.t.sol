// SPDX-License-Identifier: BSD-3-Clause
pragma solidity ^0.8.20;

import {
    CompoundJumpRateModelV2
} from "../src/CompoundJumpRateModel.sol";

contract CompoundJumpRateModelActor {
    function update(
        CompoundJumpRateModelV2 model,
        uint256 baseRatePerYear,
        uint256 multiplierPerYear,
        uint256 jumpMultiplierPerYear,
        uint256 kink
    ) external {
        model.updateJumpRateModel(
            baseRatePerYear,
            multiplierPerYear,
            jumpMultiplierPerYear,
            kink
        );
    }
}

contract CompoundJumpRateModelForgeTest {
    uint256 constant BLOCKS_PER_YEAR = 2102400;
    uint256 constant BASE = 1e18;
    uint256 constant INITIAL_KINK = 8e17;
    uint256 constant UPDATED_KINK = 5e17;

    function deploy() internal returns (CompoundJumpRateModelV2) {
        return new CompoundJumpRateModelV2(
            BLOCKS_PER_YEAR * 1000,
            3363840000,
            BLOCKS_PER_YEAR * 3000,
            INITIAL_KINK,
            address(this)
        );
    }

    function testConstructorAndPiecewiseRates() public {
        CompoundJumpRateModelV2 model = deploy();

        require(model.isInterestRateModel(), "marker");
        require(model.owner() == address(this), "owner");
        require(model.blocksPerYear() == BLOCKS_PER_YEAR, "blocks");
        require(model.baseRatePerBlock() == 1000, "base");
        require(model.multiplierPerBlock() == 2000, "multiplier");
        require(model.jumpMultiplierPerBlock() == 3000, "jump");
        require(model.kink() == INITIAL_KINK, "kink");

        require(model.utilizationRate(100, 0, 0) == 0, "zero util");
        require(model.utilizationRate(100, 100, 0) == 5e17, "half util");
        require(model.getBorrowRate(100, 100, 0) == 2000, "below kink");
        require(model.getBorrowRate(0, 100, 0) == 3200, "above kink");
        require(model.getSupplyRate(100, 100, 0, 1e17) == 900, "supply");
    }

    function testOwnerUpdateAndRollback() public {
        CompoundJumpRateModelV2 model = deploy();
        CompoundJumpRateModelActor actor = new CompoundJumpRateModelActor();

        try actor.update(
            model,
            BLOCKS_PER_YEAR * 7,
            11563200,
            BLOCKS_PER_YEAR * 13,
            UPDATED_KINK
        ) {
            revert("expected owner gate");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("only the owner may call this function.")),
                "reason"
            );
            require(model.baseRatePerBlock() == 1000, "rollback base");
        }

        model.updateJumpRateModel(
            BLOCKS_PER_YEAR * 7,
            11563200,
            BLOCKS_PER_YEAR * 13,
            UPDATED_KINK
        );

        require(model.baseRatePerBlock() == 7, "updated base");
        require(model.multiplierPerBlock() == 11, "updated multiplier");
        require(model.jumpMultiplierPerBlock() == 13, "updated jump");
        require(model.kink() == UPDATED_KINK, "updated kink");
        require(model.getBorrowRate(100, 100, 0) == 12, "at kink");
        require(model.getBorrowRate(0, 100, 0) == 18, "post jump");
    }

    function testInvalidReserveUnderflowReverts() public {
        CompoundJumpRateModelV2 model = deploy();

        try model.getBorrowRate(1, 1, 3) returns (uint256) {
            revert("expected underflow");
        } catch Panic(uint256 code) {
            require(code == 0x11, "panic code");
        }
    }
}
