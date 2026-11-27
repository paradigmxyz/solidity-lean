# Box lifecycle, ERC20 READMIT

From boxctl get_box (read-only, after the run). Times UTC. Internal labels (thread, requester) omitted.

| slot | box | id | region | created | destroyed | expiry |
| --- | --- | --- | --- | --- | --- | --- |
| A | erc20ra-47fd | box_1795726003716875307 | FRA | 2026-11-26T20:46:43.716874385Z | 2026-11-26T22:40:55.028855112Z | 2026-11-26T22:46:43.716874385Z |
| B | erc20rb-4377 | box_1795733602808459334 | FRA | 2026-11-26T22:53:22.808458893Z | 2026-11-27T00:35:57.824576086Z | 2026-11-27T00:53:22.808458893Z |
| C | erc20rc-dba6 | box_1795739763828033758 | FRA2 | 2026-11-27T00:36:03.828033217Z | 2026-11-27T02:08:40.514713183Z | 2026-11-27T02:36:03.828033217Z |

Never two at once: A destroyed 22:40:55Z before B created 22:53:22Z; B destroyed 00:35:57Z before C
created 00:36:03Z. All three destroyed before expiry. All m4-metal-large, keep_alive 2h.

Not included: the create attempts refused with SERVERS_OUT_OF_STOCK (no server assigned; each failed
record was deleted at once). Their names are not retained here.
