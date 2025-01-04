use std::{borrow::Cow, fmt::Write};

use percent_encoding::{percent_encode, AsciiSet, CONTROLS};

use crate::{windows::parse_drive, Component, Path, Prefix};

const URL_FRAGMENT: &AsciiSet = &CONTROLS.add(b' ').add(b'"').add(b'<').add(b'>').add(b'`');
const URL_PATH: &AsciiSet = &URL_FRAGMENT.add(b'#').add(b'?').add(b'{').add(b'}');
const URL_PATH_SEGMENT: &AsciiSet = &URL_PATH.add(b'/').add(b'%');

#[derive(thiserror::Error, Debug)]
pub enum PathToUrlError {
    #[error(transparent)]
    UrlParseError(#[from] url::ParseError),
    #[error("PathNotAbsoluteError {{ path = {path} }}")]
    PathNotAbsoluteError { path: Cow<'static, str> },
    #[error("NotSupportedPrefixError {{ path = {path}, prefix = {prefix} }}")]
    NotSupportedPrefixError {
        path: Cow<'static, str>,
        prefix: Cow<'static, str>,
    },
    #[error("NotSupportedFirstComponentError {{ path = {path}, comp = {comp} }}")]
    NotSupportedFirstComponentError {
        path: Cow<'static, str>,
        comp: Cow<'static, str>,
    },
}

#[inline]
pub fn to_u32(i: usize) -> Result<u32, url::ParseError> {
    if i <= u32::MAX as usize {
        Ok(i as u32)
    } else {
        Err(url::ParseError::Overflow)
    }
}

pub(crate) fn path_to_file_url_segments(
    path: &Path,
    serialization: &mut String,
) -> Result<(u32, Option<::url::Host<String>>), PathToUrlError> {
    if !path.is_absolute() {
        return Err(PathToUrlError::PathNotAbsoluteError {
            path: Cow::Owned(path.as_str().to_string()),
        });
    }
    let mut components = path.components();

    let host_start = serialization.len() + 1;
    let host_end;
    let host_internal: Option<url::Host<String>>;

    match components.next() {
        Some(Component::Prefix(ref p)) => match p.kind() {
            Prefix::Disk { drive } | Prefix::VerbatimDisk { drive } => {
                host_end = to_u32(serialization.len()).unwrap();
                host_internal = None;
                serialization.push('/');
                serialization.push(drive);
                serialization.push(':');
            }
            Prefix::UNC { server, share } | Prefix::VerbatimUNC { server, share } => {
                let host = url::Host::parse(server)?;
                write!(serialization, "{}", host).unwrap();
                host_end = to_u32(serialization.len()).unwrap();
                host_internal = Some(host);
                serialization.push('/');
                serialization.extend(percent_encode(share.as_bytes(), URL_PATH_SEGMENT));
            }
            _ => {
                return Err(PathToUrlError::NotSupportedPrefixError {
                    path: Cow::Owned(path.as_str().to_string()),
                    prefix: Cow::Owned(p.as_str().to_string()),
                });
            }
        },
        Some(Component::RootDir(_)) => {
            let host_end = to_u32(serialization.len()).unwrap();
            let mut empty = true;
            for component in components {
                empty = false;
                serialization.push('/');

                serialization.extend(percent_encode(
                    component.as_str().as_bytes(),
                    URL_PATH_SEGMENT,
                ));
            }

            if empty {
                serialization.push('/');
            }
            return Ok((host_end, None));
        }
        Some(comp) => {
            return Err(PathToUrlError::NotSupportedFirstComponentError {
                path: Cow::Owned(path.as_str().to_string()),
                comp: Cow::Owned(comp.as_str().to_string()),
            });
        }
        None => {
            return Err(PathToUrlError::NotSupportedFirstComponentError {
                path: Cow::Owned(path.as_str().to_string()),
                comp: Cow::Borrowed("null"),
            });
        }
    }

    let mut path_only_has_prefix = true;
    for component in components {
        if matches!(component, Component::RootDir(..)) {
            continue;
        }

        path_only_has_prefix = false;
        let component = component.as_str();

        serialization.push('/');
        serialization.extend(percent_encode(component.as_bytes(), URL_PATH_SEGMENT));
    }

    // A windows drive letter must end with a slash.
    if serialization.len() > host_start
        && matches!(parse_drive(&serialization[host_start..]), Ok(..))
        && path_only_has_prefix
    {
        serialization.push('/');
    }

    Ok((host_end, host_internal))
}
