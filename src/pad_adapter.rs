use std::fmt::{self, Formatter};

// Port from core::fmt::builders
pub struct PadAdapter<'a, 'buf> {
    buf: &'a mut (dyn fmt::Write + 'buf),
    on_newline: bool,
}

impl<'a, 'buf> PadAdapter<'a, 'buf> {
    pub fn new(formatter: &'a mut Formatter<'buf>) -> Self {
        Self {
            buf: formatter,
            on_newline: false,
        }
    }
}

impl fmt::Write for PadAdapter<'_, '_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for s in s.split_inclusive('\n') {
            if self.on_newline {
                self.buf.write_str("    ")?;
            }
            self.on_newline = s.ends_with('\n');
            self.buf.write_str(s)?;
        }
        Ok(())
    }

    fn write_char(&mut self, c: char) -> fmt::Result {
        if self.on_newline {
            self.buf.write_str("    ")?;
        }
        self.on_newline = c == '\n';
        self.buf.write_char(c)
    }
}
