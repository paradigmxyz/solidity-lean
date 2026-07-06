// SPDX-License-Identifier: GPL-3.0-or-later
pragma solidity ^0.8.20;

import {DapphubWETH9, DapphubWETH9Spender} from "../src/DapphubWETH9.sol";

contract DapphubWETH9ForgeTest {
    receive() external payable {}

    function testDepositReceiveAndTotalSupply() public {
        DapphubWETH9 weth = new DapphubWETH9();

        weth.deposit{value: 5}();
        require(weth.balanceOf(address(this)) == 5, "deposit balance");
        require(weth.totalSupply() == 5, "deposit supply");

        (bool ok, ) = address(weth).call{value: 7}("");
        require(ok, "receive");
        require(weth.balanceOf(address(this)) == 12, "receive balance");
        require(weth.totalSupply() == 12, "receive supply");
    }

    function testWithdrawSuccessAndFailure() public {
        DapphubWETH9 weth = new DapphubWETH9();

        weth.deposit{value: 10}();
        weth.withdraw(4);
        require(weth.balanceOf(address(this)) == 6, "withdraw balance");
        require(address(weth).balance == 6, "withdraw supply");

        (bool ok, ) =
            address(weth).call(abi.encodeWithSelector(weth.withdraw.selector, 7));
        require(!ok, "withdraw failed");
        require(weth.balanceOf(address(this)) == 6, "failed balance");
    }

    function testApproveTransferTransferFromAndMaxAllowance() public {
        DapphubWETH9 weth = new DapphubWETH9();
        DapphubWETH9Spender spender = new DapphubWETH9Spender();

        weth.deposit{value: 20}();
        require(weth.transfer(address(0xbeef), 3), "transfer");
        require(weth.balanceOf(address(this)) == 17, "transfer from");
        require(weth.balanceOf(address(0xbeef)) == 3, "transfer to");

        require(weth.approve(address(spender), 8), "approve");
        require(weth.allowance(address(this), address(spender)) == 8, "allowance");
        require(
            spender.spend(weth, address(this), address(0xcafe), 5),
            "spend"
        );
        require(weth.allowance(address(this), address(spender)) == 3, "spent");
        require(weth.balanceOf(address(this)) == 12, "spender from");
        require(weth.balanceOf(address(0xcafe)) == 5, "spender to");

        require(weth.approve(address(spender), type(uint256).max), "approve max");
        require(
            spender.spend(weth, address(this), address(0xf00d), 4),
            "spend max"
        );
        require(
            weth.allowance(address(this), address(spender)) == type(uint256).max,
            "max kept"
        );
    }

    function testTransferFromFailuresDoNotMutate() public {
        DapphubWETH9 weth = new DapphubWETH9();
        DapphubWETH9Spender spender = new DapphubWETH9Spender();

        weth.deposit{value: 2}();
        require(weth.approve(address(spender), 1), "approve");

        try spender.spend(weth, address(this), address(0xbeef), 2) {
            revert("expected allowance failure");
        } catch {
            require(weth.balanceOf(address(this)) == 2, "allowance balance");
            require(weth.allowance(address(this), address(spender)) == 1, "allowance");
        }

        try weth.transfer(address(0xbeef), 3) {
            revert("expected balance failure");
        } catch {
            require(weth.balanceOf(address(this)) == 2, "balance kept");
            require(weth.balanceOf(address(0xbeef)) == 0, "target kept");
        }
    }
}
