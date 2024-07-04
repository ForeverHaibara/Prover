import re

class ProofEnvironment():
    is_gradio = False

class Proof():
    def __init__(self, content = '') -> None:
        self.content = content

    def __str__(self) -> str:
        content = str(self.content)
        if ProofEnvironment.is_gradio:
            replacement = {
                '\n': ' \n\n ',
                '$$': '$',
                '&': ' ',
                '\\\\': ' $ \n\n  $',
                '\\begin{aligned}': '',
                '\\end{aligned}': '',
                '\\left\\{': '',
                '\\right.': '',
                # '\\sum': '\\displaystyle\\sum',
                # '\\int': '\\displaystyle\\int',
                # '\\lim': '\\displaystyle\\lim',
            }

            for k,v in replacement.items():
                content = content.replace(k,v)

            content = re.sub('\$(.*?)\$', '$\\\displaystyle \\1$', content, flags=re.DOTALL)

        return content

    def _repr_latex_(self) -> str:
        content =  self.content

        if content.startswith('$$'):
            return content

        content = content.replace('\n',' \\\\ & ').replace('$','')
        content = '$$\\begin{aligned}& %s\\end{aligned}$$'%content

        return content
