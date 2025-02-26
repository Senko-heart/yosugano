#![cfg(target_endian = "little")]
#![feature(let_chains)]

#[cfg(debug_assertions)]
mod debug;
mod ioex;
mod parse;
mod reverse;

use std::fs;
use std::io;
use std::panic;
use std::path::Path;
use std::process::ExitCode;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::Relaxed;
use std::thread;

use encoding_rs::SHIFT_JIS;

use ioex::ReadEx;

fn main() -> ExitCode {
    #[cfg(panic = "abort")] {
        panic::set_hook(Box::new(|info| {
            let location = info.location().unwrap();
            let msg = if let Some(s) = info.payload().downcast_ref::<&str>() {
                s
            } else if let Some(s) = info.payload().downcast_ref::<String>() {
                s.as_str()
            } else {
                "Box<dyn Any>"
            };
            let th = thread::current();
            let name = th.name().unwrap_or("<unnamed>");
            eprintln!("thread '{name}' panicked at {location}:\n{msg}");
        }));
    }
    
    if let Err(e) = decompile() {
        eprintln!("io error: {e}");
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}

fn decompile() -> io::Result<()> {
    let path = std::env::args_os().nth(1);
    let path = path.as_deref().map_or(Path::new("yosuga.csx"), <_>::as_ref);
    let dir = path.file_stem().map_or(path, <_>::as_ref);
    let file = std::fs::read(path)?;
    let mut data = file.as_slice();

    let csx = match data.read_data::<parse::CotophaData>() {
        Ok(csx) => csx,
        Err(e) => {
            return Err(io::Error::new(
                e.kind(),
                format!("{e} (byte offset: {})", file.len() - data.len()),
            ))
        }
    };
    let sd = reverse::SourceDecompiler::new(&csx);
    let source = reverse::Source::new(sd);
    let (ref source_str, ref source_ix) = source.to_contents();

    fs::create_dir_all(dir)?;
    let threads = thread::available_parallelism()?.get();
    let n = &AtomicUsize::new(0);
    thread::scope(|s| {
        let mut handles = Vec::from_iter((0..threads).map(|_| {
            s.spawn(|| loop {
                let n = n.fetch_add(1, Relaxed);
                let Some(&ix) = source_ix.get(n) else {
                    return io::Result::Ok(());
                };
                let name = match n {
                    0 => "definitions.ch",
                    1 => "variables.cos",
                    _ => &format!("file-{}.cos", n - 1),
                };
                let (contents, _, errors) = SHIFT_JIS.encode(&source_str[ix]);
                assert!(!errors);
                fs::write(dir.join(name), contents)?;
            })
        }))
        .into_iter();
        handles.try_for_each(|h| h.join().unwrap_or_else(|e| panic::resume_unwind(e)))
    })?;

    Ok(())
}
