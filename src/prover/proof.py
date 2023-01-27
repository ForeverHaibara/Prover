class Proof():
    def __init__(self, content = '') -> None:
        self.content = content

    def __str__(self) -> str:
        return str(self.content)

    def _repr_latex_(self) -> str:
        content =  self.content

        if content.startswith('$$'):
            return content

        content = content.replace('\n',' \\\\ & ').replace('$','')
        content = '$$\\begin{aligned}& %s\\end{aligned}$$'%content

        return content
