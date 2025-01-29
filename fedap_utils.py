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

def simulate_nodes_computation(el_splits: list):
    """
    Simulation of a federated computation FM. Every split is processed independently. Footprint Matrices and of
    1-length loops are collected and returned. This simulates sharing the partial results with the master
    aggregator node.

    Parameters
    ----------
    el_splits
        List of event log

    Returns
    FTs
        list of footprint matrices
    oneL_inputs_dic
        Dictionary of oneL inputs
    oneL_outputs_dic
        Dictionary of oneL outputs
    loop_one_list
        List of 1-length loop events
    -------

    """
    oneL_inputs_list = []
    oneL_outputs_list = []
    loop_one_tot_list = []
    FTs = []
    for el in el_splits:
        net_split, initial_marking_split, final_marking_split, footprint_matrix_split, loop_one_list_split, oneL_inputs_split, oneL_outputs_split = apply_monocentric(el)
        oneL_inputs_list.append(oneL_inputs_split)
        oneL_outputs_list.append(oneL_outputs_split)
        loop_one_tot_list = list(set(loop_one_tot_list + loop_one_list_split))
        FTs.append(footprint_matrix_split)
    oneL_outputs_dic = update_io_dict(oneL_outputs_list)
    oneL_inputs_dic = update_io_dict(oneL_inputs_list)
    return FTs, oneL_inputs_dic, oneL_outputs_dic, loop_one_tot_list