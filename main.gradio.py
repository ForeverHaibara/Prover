# https://github.com/ForeverHaibara

# pip install gradio --upgrade
# pip install sympy

import gradio as gr
import sympy as sp

from src.prover.proof import ProofEnvironment, Proof
from src.prover.derivative import solve as solve_derivative
from src.prover.trig.inequality import prove_trig_extrema

# Cater for gradio's need. gradio == 3.44.4
ProofEnvironment.is_gradio = True


class Page:
    def __init__(self):
        self.components = []
        self.solution = Proof()
    def enabled(self):
        # https://github.com/gradio-app/gradio/issues/2154
        # return dict((x, {"visible": True, "__type__": "update"}) for x in self.components)
        return dict((x, gr.update(visible=True)) for x in self.components)
    def disabled(self):
        return dict((x, gr.update(visible=False)) for x in self.components)

    def solve(self):
        return {self.output: str(self.solution), self.output_latex: str(self.solution.content)}

class TrigSolver(Page):
    def __init__(self):
        with gr.Tab("Trig Solver"):
            with gr.Row():
                self.formula_input = gr.Textbox(label="Function", placeholder="Input some trignometric functions like sin(x)+2*cos(x)", scale=3)
                self.compute_btn = gr.Button("Solve", scale=1, variant="primary")
            with gr.Row():
                self.method_input = gr.Radio(choices=["auto", "derv", "sos"], label="Method", value = "auto")
                self.domain_start = gr.Textbox(label="Domain Start (in radians)")
                self.domain_end = gr.Textbox(label="Domain End (in radians)")

            with gr.Tabs():
                with gr.Tab("Display"):
                    self.output = gr.Markdown()
                with gr.Tab("LaTeX"):
                    self.output_latex = gr.TextArea(label="Result", show_copy_button=True)

            self.compute_btn.click(fn = self.solve, inputs = [self.formula_input, self.method_input, self.domain_start, self.domain_end], outputs = [self.output, self.output_latex])
            self.components = [self.formula_input, self.method_input, self.domain_start, self.domain_end, self.output, self.compute_btn]

    def solve(self, formula, method, domain_start, domain_end):
        def _sympifier(x):
            x = x.strip()
            if len(x) == 0: return None
            return sp.sympify(x)
        self.solution = prove_trig_extrema(
            formula, 
            domain = [_sympifier(domain_start), _sympifier(domain_end)],
            method = method
        )
        return super().solve()

class Approximant(Page):
    def __init__(self):
        with gr.Tab("Approximant"):
            with gr.Row():
                self.formula_input = gr.Textbox(label="Function", placeholder="Input some functions like exp(5/4)-7/2", scale=3)
                self.compute_btn = gr.Button("Solve", scale=1, variant="primary")
            self.method_input = gr.Radio(choices=["taylor", "integral"], label="Method", value = "taylor")

            with gr.Tabs():
                with gr.Tab("Display"):
                    self.output = gr.Markdown()
                with gr.Tab("LaTeX"):
                    self.output_latex = gr.TextArea(label="Result", show_copy_button=True)
            self.compute_btn.click(fn = self.solve, inputs = [self.formula_input, self.method_input], outputs = [self.output, self.output_latex])
            self.components = [self.formula_input, self.method_input, self.output, self.compute_btn]

    def solve(self, formula, method):
        self.solution = solve_derivative(formula, method = method)
        return super().solve()


pageinfo = {
    'pages': {"Trig Solver": TrigSolver, "Approximant": Approximant},
    'page': "Trig Solver",
}

with gr.Blocks() as demo:
    for name, page_class in pageinfo['pages'].items():
        pageinfo['pages'][name] = page_class()


demo.footer_html = '<a href="https://github.com/ForeverHaibara"><i class="fab fa-github"></i></a>'
demo.launch()