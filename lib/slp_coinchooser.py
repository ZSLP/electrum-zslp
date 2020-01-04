from electrum_zclassic.util import NotEnoughFundsSlp, NotEnoughUnfrozenFundsSlp
from electrum_zclassic import slp

class SlpCoinChooser:

    @staticmethod
    def select_coins(wallet, token_id, amount, config, isInvoice=False, *, domain=None):
        amt = amount or 0
        valid_bal, _, _, unfrozen_bal, _ = wallet.get_slp_token_balance(token_id, config)

        if amt > valid_bal:
            raise NotEnoughFundsSlp("Not enough token funds.")
        if valid_bal >= amt > unfrozen_bal:
            raise NotEnoughUnfrozenFundsSlp("Not enough unfrozen token funds.")

        slp_coins = wallet.get_slp_spendable_coins(token_id, domain, config, isInvoice)
        slp_coins = sorted(slp_coins, key=lambda k: -k['token_value'])

        selected_slp_coins = []
        total_amt_added = 0
        for coin in slp_coins:
            if total_amt_added < amt:
                selected_slp_coins.append(coin)
                total_amt_added += coin['token_value']
            else:
                break

        token_outputs_amts = []
        slp_op_return_msg = None
        if total_amt_added > 0:
            token_outputs_amts.append(amt)
            token_change = total_amt_added - amt
            if token_change > 0:
                token_outputs_amts.append(token_change)
            token_type = wallet.token_types[token_id]['class']
            slp_op_return_msg = slp.buildSendOpReturnOutput_V1(token_id, token_outputs_amts, token_type)

        if selected_slp_coins:
            assert slp_op_return_msg

        return (selected_slp_coins, slp_op_return_msg)

