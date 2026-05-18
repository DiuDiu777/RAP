use std::fmt;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum PrimitiveSpFamily {
    Layout,
    Pointer,
    Content,
    AliasLifetime,
    Misc,
    Compound,
    FunctionSpecific,
    SystemSpecific,
    Unknown,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum PrimitiveSpKind {
    Align,
    DoubleAlign,
    Size,
    NonZeroSize,
    NoPadding,
    NonNull,
    Null,
    Allocated,
    InBound,
    NonOverlap,
    ValidNum,
    ValidString,
    ValidCStr,
    Init,
    Unwrap,
    Typed,
    NotOwned,
    Alias,
    Alive,
    Pinned,
    NonVolatile,
    Opened,
    TraitCopy,
    Unreachable,
    ValidPtr,
    ValidPtr2Ref,
    Layout,
    ValidSlice,
    ValidTraitObj,
    FunctionSpecific,
    SystemSpecific,
    Unknown(String),
}

pub fn normalize_tag(tag: &str) -> String {
    tag.trim().trim_end_matches('|').trim().to_owned()
}

impl PrimitiveSpKind {
    pub fn from_tag(tag: &str) -> Self {
        let tag = normalize_tag(tag);
        match tag.as_str() {
            "Align" | "Aligned" => Self::Align,
            "DoubleAlign" | "DoubleAligned" => Self::DoubleAlign,
            "Size" => Self::Size,
            "!Size" => Self::NonZeroSize,
            "!Padding" | "NoPadding" => Self::NoPadding,
            "!Null" | "NonNull" => Self::NonNull,
            "Null" => Self::Null,
            "Allocated" => Self::Allocated,
            "InBound" | "InBounded" => Self::InBound,
            "!Overlap" | "NonOverlap" => Self::NonOverlap,
            "ValidNum" => Self::ValidNum,
            "ValidString" => Self::ValidString,
            "ValidCStr" => Self::ValidCStr,
            "Init" => Self::Init,
            "Unwrap" => Self::Unwrap,
            "Typed" => Self::Typed,
            "!Owned" | "Ownning" | "Owning" | "NotOwned" => Self::NotOwned,
            "Alias" => Self::Alias,
            "Alive" => Self::Alive,
            "Pinned" => Self::Pinned,
            "!Volatile" | "NonVolatile" => Self::NonVolatile,
            "Opened" => Self::Opened,
            "CopyTrait" | "TraitCopy" => Self::TraitCopy,
            "!Reachable" | "Unreachable" => Self::Unreachable,
            "ValidPtr" => Self::ValidPtr,
            "ValidPtr2Ref" | "Ptr2Ref" => Self::ValidPtr2Ref,
            "Layout" => Self::Layout,
            "ValidSlice" => Self::ValidSlice,
            "ValidTraitObj" => Self::ValidTraitObj,
            "Function_sp" | "FunctionSP" => Self::FunctionSpecific,
            "System_sp" | "SystemSP" => Self::SystemSpecific,
            _ => Self::Unknown(tag),
        }
    }

    pub fn family(&self) -> PrimitiveSpFamily {
        match self {
            Self::Align | Self::DoubleAlign | Self::Size | Self::NonZeroSize | Self::NoPadding => {
                PrimitiveSpFamily::Layout
            }
            Self::NonNull
            | Self::Null
            | Self::Allocated
            | Self::InBound
            | Self::NonOverlap
            | Self::ValidPtr
            | Self::ValidPtr2Ref
            | Self::Layout
            | Self::ValidSlice
            | Self::ValidTraitObj => PrimitiveSpFamily::Pointer,
            Self::ValidNum
            | Self::ValidString
            | Self::ValidCStr
            | Self::Init
            | Self::Unwrap
            | Self::Typed => PrimitiveSpFamily::Content,
            Self::NotOwned | Self::Alias | Self::Alive => PrimitiveSpFamily::AliasLifetime,
            Self::Pinned
            | Self::NonVolatile
            | Self::Opened
            | Self::TraitCopy
            | Self::Unreachable => PrimitiveSpFamily::Misc,
            Self::FunctionSpecific => PrimitiveSpFamily::FunctionSpecific,
            Self::SystemSpecific => PrimitiveSpFamily::SystemSpecific,
            Self::Unknown(_) => PrimitiveSpFamily::Unknown,
        }
    }

    pub fn is_value_fuzzable(&self) -> bool {
        matches!(
            self,
            Self::ValidNum | Self::ValidString | Self::ValidCStr | Self::Unwrap
        )
    }

    pub fn is_memory_state_fuzzable(&self) -> bool {
        matches!(
            self,
            Self::Align
                | Self::DoubleAlign
                | Self::NonNull
                | Self::Null
                | Self::Allocated
                | Self::InBound
                | Self::NonOverlap
                | Self::Init
                | Self::Typed
                | Self::NotOwned
                | Self::Alias
                | Self::Alive
                | Self::ValidPtr
                | Self::ValidPtr2Ref
        )
    }
}

impl fmt::Display for PrimitiveSpKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Align => write!(f, "Align"),
            Self::DoubleAlign => write!(f, "DoubleAlign"),
            Self::Size => write!(f, "Size"),
            Self::NonZeroSize => write!(f, "NonZeroSize"),
            Self::NoPadding => write!(f, "NoPadding"),
            Self::NonNull => write!(f, "NonNull"),
            Self::Null => write!(f, "Null"),
            Self::Allocated => write!(f, "Allocated"),
            Self::InBound => write!(f, "InBound"),
            Self::NonOverlap => write!(f, "NonOverlap"),
            Self::ValidNum => write!(f, "ValidNum"),
            Self::ValidString => write!(f, "ValidString"),
            Self::ValidCStr => write!(f, "ValidCStr"),
            Self::Init => write!(f, "Init"),
            Self::Unwrap => write!(f, "Unwrap"),
            Self::Typed => write!(f, "Typed"),
            Self::NotOwned => write!(f, "NotOwned"),
            Self::Alias => write!(f, "Alias"),
            Self::Alive => write!(f, "Alive"),
            Self::Pinned => write!(f, "Pinned"),
            Self::NonVolatile => write!(f, "NonVolatile"),
            Self::Opened => write!(f, "Opened"),
            Self::TraitCopy => write!(f, "TraitCopy"),
            Self::Unreachable => write!(f, "Unreachable"),
            Self::ValidPtr => write!(f, "ValidPtr"),
            Self::ValidPtr2Ref => write!(f, "ValidPtr2Ref"),
            Self::Layout => write!(f, "Layout"),
            Self::ValidSlice => write!(f, "ValidSlice"),
            Self::ValidTraitObj => write!(f, "ValidTraitObj"),
            Self::FunctionSpecific => write!(f, "FunctionSpecific"),
            Self::SystemSpecific => write!(f, "SystemSpecific"),
            Self::Unknown(tag) => write!(f, "Unknown({tag})"),
        }
    }
}
