class REPL:
    # default_jvm_params = ["-cp", str(TOOLS_DIR / "tla2tools.jar")]

    @classmethod
    def run(cls) -> None:
        pass

    #     import sys

    #     result = subprocess.run(
    #         ["java"] + cls.default_jvm_params + ["tlc2.REPL"],
    #         stdin=sys.stdin,
    #         stdout=sys.stdout,
    #         stderr=subprocess.PIPE,
    #         text=True,
    #     )

    #     if result.stderr:
    #         raise RuntimeError(result.stderr)
