# https://github.com/ForeverHaibara

# pip install gradio --upgrade
# pip install sympy

import gradio as gr
import sympy as sp

from src.prover.proof import ProofEnvironment
from src.prover.trig.inequality import prove_trig_extrema

# Cater for gradio's need. gradio == 3.44.4
ProofEnvironment.is_gradio = True

def trig_solver(formula, method, domain_start, domain_end):
    def _sympifier(x):
        x = x.strip()
        if len(x) == 0: return None
        return sp.sympify(x)
    solution = prove_trig_extrema(
        formula, 
        domain = [_sympifier(domain_start), _sympifier(domain_end)],
        method = method
    )
    return str(solution)

with gr.Blocks() as demo:
    formula_input = gr.Textbox(label="Function", placeholder="Input some trignometric function like sin(x)+2*cos(x)")
    with gr.Row():
        method_input = gr.Radio(choices=["auto", "derv", "sos"], label="Method", value = "auto")
        domain_start = gr.Textbox(label="Domain Start (in radians)")
        domain_end = gr.Textbox(label="Domain End (in radians)")
    output = gr.Markdown()
    compute_btn = gr.Button("Solve")
    compute_btn.click(fn = trig_solver, inputs = [formula_input, method_input, domain_start, domain_end], outputs = output)

    demo.footer_html = '<a href="https://github.com/ForeverHaibara"><i class="fab fa-github"></i></a>'
demo.launch()
