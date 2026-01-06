use crate::driver::compiler::CompilePhase;
use crate::driver::{cli::CompileConfig, compiler::CompilerDriver};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir_dumper::{MirDumpConfig, MirDumper};

    /// helper function to setup compiler driver with given source code
    fn setup_mir(source: &str) -> String {
        let phase = CompilePhase::Mir;
        let config = CompileConfig::from_virtual_file(source.to_string(), phase);
        let mut driver = CompilerDriver::from_config(config);
        let mut out = match driver.run_pipeline(phase) {
            Ok(out) => out,
            Err(_) => panic!("failed to run: {:?}", driver.get_diagnostics()),
        };
        let first = out.units.first_mut().unwrap();
        let artifact = first.1;

        // Get the complete semantic analysis output
        let sema_output = match artifact.sema_output.clone() {
            Some(sema_output) => sema_output,
            None => {
                let d = driver.get_diagnostics();
                println!("{:?}", d);
                panic!("No semantic output available");
            }
        };

        // Output MIR dump to string
        let dump_config = MirDumpConfig { include_header: false };
        let dumper = MirDumper::new(&sema_output, &dump_config);

        dumper.generate_mir_dump().unwrap()
    }

    #[test]
    fn test_function_redefinition_with_prototype() {
        let source = r#"
            int x;
            int x = 3;
            int x;

            int main();

            void *
            foo()
            {
                return &main;
            }

            int
            main()
            {
                if (x != 3)
                    return 0;

                x = 0;
                return x;
            }
        "#;

        let mir_dump = setup_mir(source);
        // We just want to ensure it compiles without panic.
        // But we can also check the output to be sure.
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32
        type %t1 = ptr<%t2>
        type %t2 = void
        type %t3 = ptr<%t4>
        type %t4 = fn() -> %t0

        global @x: i32 = cast<i32>(const 3)

        fn main() -> i32
        {
          locals {
            %1: i32
          }

          bb2:
            %1 = @x != cast<i32>(const 3)
            cond_br %1, bb3, bb4

          bb3:
            return cast<i32>(const 0)

          bb4:
            br bb5

          bb5:
            @x = cast<i32>(const 0)
            return @x
        }

        fn foo() -> ptr<void>
        {

          bb1:
            return cast<ptr<void>>(const main)
        }
        ");
    }
}
