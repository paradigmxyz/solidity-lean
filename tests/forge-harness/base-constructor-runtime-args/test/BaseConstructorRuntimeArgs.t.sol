// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/BaseConstructorRuntimeArgs.sol";

interface Vm {
    function roll(uint256 blockNumber) external;
    function deal(address account, uint256 newBalance) external;
    function mockCall(address callee, bytes calldata data, bytes calldata returnData) external;
    function expectRevert() external;
}

contract BaseConstructorRuntimeArgsForgeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function testEnvironmentAndFileScopeRuntimeArgs() public {
        vm.roll(50);
        BlockArg blockArg = new BlockArg();
        require(blockArg.seed() == 51);

        SenderArg senderArg = new SenderArg();
        require(senderArg.seed() == uint160(address(this)));

        FreeCallArg freeCallArg = new FreeCallArg();
        require(freeCallArg.seed() == 57);
    }

    function testValueBalanceAndConstructorParameterArgs() public {
        ValueArg valueArg = new ValueArg{value: 9}();
        require(valueArg.seed() == 12);

        NonpayableValueArg nonpayableValueArg = new NonpayableValueArg();
        require(nonpayableValueArg.seed() == 4);

        ModifierParamArg modifierParamArg = new ModifierParamArg(8);
        require(modifierParamArg.seed() == 9);

        vm.deal(address(this), 100 ether);
        BalanceArg balanceArg = new BalanceArg{value: 10}();
        require(balanceArg.seed() == 10);
    }

    function testUsingAndExternalRuntimeArgs() public {
        FreeUsingArg freeUsingArg = new FreeUsingArg();
        require(freeUsingArg.seed() == 6);

        LibraryUsingArg libraryUsingArg = new LibraryUsingArg();
        require(libraryUsingArg.seed() == 5);

        ContractUsingArg contractUsingArg = new ContractUsingArg();
        require(contractUsingArg.seed() == 15);

        vm.mockCall(
            address(0xbeef),
            abi.encodeWithSelector(HeaderOracle.seed.selector),
            abi.encode(uint256(41))
        );
        ExternalCallArg externalCallArg = new ExternalCallArg();
        require(externalCallArg.seed() == 41);
    }

    function testThisCallInHeaderRevertsInConcreteEvm() public {
        vm.expectRevert();
        new ThisCallArg();
    }
}
