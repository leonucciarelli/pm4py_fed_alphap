import pandas as pd
from pm4py.objects.conversion.log import converter as log_converter
import pm4py

def load_convert_el(el_path, case_id, activity_key, timestamp_key):
    df = pd.read_csv(filepath_or_buffer=el_path, dtype={case_id: int, activity_key: str})
    df[timestamp_key] = pd.to_datetime(df[timestamp_key])
    event_log = pm4py.format_dataframe(df, case_id=case_id, activity_key=activity_key, timestamp_key=timestamp_key)
    event_log = log_converter.apply(event_log)
    return event_log, df

def apply_monocentric(event_log):
    net, initial_marking, final_marking, footprint_matrix, loop_one_list, oneL_inputs, oneL_outputs, rels = pm4py.algo.discovery.alpha.algorithm.apply(event_log, variant=pm4py.algo.discovery.alpha.algorithm.Variants.ALPHA_VERSION_PLUS)
    pm4py.view_petri_net(net, initial_marking, final_marking)
    print(f'Relations:\n {pretty_print_dict(rels)}')
    print(f'Length One Loop Inputs:\n {pretty_print_dict(oneL_inputs)}')
    print(f'Length One Loop Outputs:\n {pretty_print_dict(oneL_outputs)}')
    return net, initial_marking, final_marking, footprint_matrix, loop_one_list, oneL_inputs, oneL_outputs

def pretty_print_dict(d, indent=0):
    res = ""
    for k, v in d.items():
        res += "\t"*indent + str(k) + "\n"
        if isinstance(v, dict):
            res += pretty_print_dict(v, indent+1)
        else:
            res += "\t"*(indent+1) + str(v) + "\n"
    return res

def update_io_dict(oneL_io_list) -> dict:
    oneL_io_dic = {}
    for oneL_io in oneL_io_list:
        for event_key, event_value in oneL_io.items():
            if event_key in oneL_io_dic:
                oneL_io_dic[event_key].add(event_value)
            else:
                oneL_io_dic[event_key] = event_value
    return oneL_io_dic