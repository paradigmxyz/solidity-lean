// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import "../src/FrontendFrontier.sol";

contract FrontendFrontierForgeTest {
    FrontendFrontierScalarValues private transientBoundary;

    function setUp() public {
        transientBoundary = new FrontendFrontierScalarValues(90);
        transientBoundary.transientWrite(77);
    }

    function testOverridesFunctionTypesAndLiteralForms() public {
        FrontendFrontierImpl target = new FrontendFrontierImpl(5);
        FrontendFrontierImpl other = new FrontendFrontierImpl(9);
        FrontendFrontierOverrideDiamond diamond =
            new FrontendFrontierOverrideDiamond();
        FrontendFrontierModifierOverride modifierOverride =
            new FrontendFrontierModifierOverride();
        FrontendFrontierInterfaceImpl interfaceImpl =
            new FrontendFrontierInterfaceImpl();
        FrontendFrontierUsingFunctionList usingList =
            new FrontendFrontierUsingFunctionList();
        FrontendFrontierGlobalUsing globalUsing =
            new FrontendFrontierGlobalUsing();
        FrontendFrontierScalarOps scalarOps =
            new FrontendFrontierScalarOps();
        FrontendFrontierScalarValues scalarValues =
            new FrontendFrontierScalarValues(40);
        FrontendFrontierConstructorUsing constructorUsing =
            new FrontendFrontierConstructorUsing(40);
        FrontendFrontierFunctionTypeVariants functionTypeVariants =
            new FrontendFrontierFunctionTypeVariants();
        FrontendFrontierFunctionTypes caller =
            new FrontendFrontierFunctionTypes();

        require(target.value() == 5, "value");
        require(target.compute(7) == 13, "compute");
        require(target.values(1) == 2, "constant length getter");
        require(target.sumValues() == 6, "constant length sum");
        require(diamond.pick() == 9, "override bases");
        require(modifierOverride.gated() == 11, "modifier override");
        require(interfaceImpl.ifaceValue() == 78, "interface impl");
        require(usingList.run(41) == 42, "using function list");
        require(globalUsing.run(20, 22) == 42, "using global");
        require(globalUsing.operatorSweep() == 992, "using operators");
        require(scalarValues.immutableValue() == 40, "immutable value");
        require(constructorUsing.result() == 83, "constructor using");
        require(scalarOps.operatorFrontier() == 93, "operator frontier");
        require(scalarOps.unitFrontier() == 21, "unit frontier");
        require(scalarValues.storageRef() == 41, "storage ref");
        require(scalarValues.transientRoundTrip(12) == 12, "transient");
        scalarValues.transientWrite(77);
        require(scalarValues.transientRead() == 77, "transient message");
        require(
            functionTypeVariants.internalPureRun(41) == 42,
            "internal function type"
        );
        require(caller.callGetter(target.value) == 5, "getter");
        require(caller.same(target.value, target.value), "same");
        require(!caller.same(target.value, other.value), "different");

        (bytes memory raw, string memory text, uint256 unitValue) =
            caller.literalFrontier();
        require(keccak256(raw) == keccak256(hex"1234"), "hex");
        require(keccak256(bytes(text)) == keccak256(bytes("hi")), "unicode");
        require(unitValue == 120, "unit");
    }

    function testTransientClearsAcrossTopLevelCalls() public view {
        require(transientBoundary.transientRead() == 0, "transient boundary");
    }
}
