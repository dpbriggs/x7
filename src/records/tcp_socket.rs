use crate::{
    exact_len,
    symbols::{Expr, Function, LispResult, SymbolTable},
};
use anyhow::anyhow;
use std::{io::BufReader, net::TcpListener};
use std::{
    io::{BufRead, Write},
    net::TcpStream,
};

use super::{struct_record::StructRecord, RecordDoc};

pub(crate) struct TcpListenerRecord {
    // TODO: Move these options into their own struct.
    tcp_listener: Option<TcpListener>,
    accept_fn: Option<Function>,
    symbol_table: Option<SymbolTable>,
    id: u64,
}

impl Default for TcpListenerRecord {
    fn default() -> Self {
        TcpListenerRecord {
            tcp_listener: None,
            accept_fn: None,
            symbol_table: None,
            id: rand::random(),
        }
    }
}

impl PartialEq for TcpListenerRecord {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl TcpListenerRecord {
    pub(crate) const RECORD_NAME: &'static str = "TcpListenerRecord";

    fn bind(args: Vec<Expr>, symbol_table: &SymbolTable) -> LispResult<Self> {
        exact_len!(args, 2);
        let address = args[0].get_string()?;
        let accept_fn = args[1].get_function()?.clone();
        let tcp_listener = TcpListener::bind(&address)
            .map_err(|e| anyhow!("Could not bind to network address! {:?}", e))?;
        Ok(TcpListenerRecord {
            tcp_listener: Some(tcp_listener),
            accept_fn: Some(accept_fn),
            symbol_table: Some(symbol_table.clone()),
            id: rand::random(),
        })
    }

    fn handle_incoming(&self, incoming: TcpStream) -> LispResult<()> {
        let read_stream = incoming;
        let mut write_stream = read_stream.try_clone().unwrap();
        let line_stream = BufReader::new(read_stream);
        let mut lines = Vec::new();
        for line in line_stream.lines() {
            let line = line.map_err(|e| anyhow!("Failed to read from connection! {:?}", e))?;
            if !line.is_empty() {
                lines.push(line);
            } else {
                let ff = self.accept_fn.as_ref().unwrap();
                let sym = self.symbol_table.as_ref().unwrap();
                let lines_expr = Expr::Tuple(lines.iter().cloned().map(Expr::string).collect());
                let res = ff
                    .call_fn(im::Vector::unit(lines_expr), sym)?
                    .get_string()?;
                write_stream
                    .write_all(res.as_bytes())
                    .map_err(|e| anyhow!("Failed to write response {} \n\n {:?}", res, e))?;
                return Ok(());
            }
        }
        Ok(())
    }

    fn listen(&self) -> LispResult<Expr> {
        // TODO: Run this in a different thread!
        for incoming in self.tcp_listener.as_ref().unwrap().incoming() {
            let incoming = incoming.map_err(|e| anyhow!("Failed to accept connection! {:?}", e))?;
            self.handle_incoming(incoming)?;
        }
        Ok(Expr::Nil)
    }

    fn display(&self) -> String {
        format!(
            "TcpListenerRecord<accept={:?}>",
            self.accept_fn.as_ref().unwrap()
        )
    }

    pub(crate) fn make() -> Expr {
        StructRecord::record_builder(TcpListenerRecord::RECORD_NAME)
            .init_fn(&TcpListenerRecord::bind)
            .display_with(&TcpListenerRecord::display)
            .add_method("listen", TcpListenerRecord::listen)
            .build()
    }
}

impl RecordDoc for TcpListenerRecord {
    fn name() -> &'static str {
        "TcpListenerRecord"
    }

    fn type_doc() -> &'static str {
        "Tcp Socket Server TBD"
    }

    fn method_doc() -> &'static [(&'static str, &'static str)] {
        &[]
    }
}
