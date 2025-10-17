from abc import ABC


class Tool(ABC):
    def __init__(self, name: str) -> None:
        self.name = name
