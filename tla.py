import rich_click as click

@click.group(
    name="tla",
    context_settings={"help_option_names": ["-h", "--help"],"auto_envvar_prefix": "TLA_"}
)
@click.version_option(version="0.1.0", prog_name="tla")
def cli(**kwargs) -> None:
    """
    Command-line tool to simplify working with TLA+.
    """
    pass

if __name__ == "__main__":
    cli()
