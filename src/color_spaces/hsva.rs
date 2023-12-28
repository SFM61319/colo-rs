//! An HSVA color.
//!
//! This module contains the [`Hsva`] color space type, and several error types
//! that may result from working with [`Hsva`] colors.
//!
//! # Examples
//!
//! You can create a new [`Hsva`] color from individual hue, saturation, value,
//! and alpha values:
//!
//! ```
//! let red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 1.0);
//! let green = colo_rs::Hsva::from([120.0, 1.0, 1.0]);
//! let blue = colo_rs::Hsva::from([240.0, 1.0, 1.0, 1.0]);
//! let black = colo_rs::Hsva::from((0.0, 0.0, 0.0));
//! let white = colo_rs::Hsva::from((0.0, 0.0, 1.0, 1.0));
//! ```
//!
//! Or use the default transparent black color:
//!
//! ```
//! let transparent = colo_rs::Hsva::default();
//! ```
//!
//! Check if an [`Hsva`] color is transparent or not:
//!
//! ```
//! let red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 1.0);
//! let green = colo_rs::Hsva::new(120.0, 1.0, 1.0, 1.0);
//! let blue = colo_rs::Hsva::new(240.0, 1.0, 1.0, 1.0);
//! let black = colo_rs::Hsva::new(0.0, 0.0, 0.0, 1.0);
//! let white = colo_rs::Hsva::new(0.0, 0.0, 1.0, 1.0);
//! let translucent_gray = colo_rs::Hsva::new(0.0, 0.0, 0.5, 0.5);
//! let transparent = colo_rs::Hsva::default();
//!
//! assert!(!red.is_transparent());
//! assert!(!green.is_transparent());
//! assert!(!blue.is_transparent());
//! assert!(!black.is_transparent());
//! assert!(!white.is_transparent());
//! assert!(!translucent_gray.is_transparent());
//! assert!(transparent.is_transparent());
//! ```
//!
//! Check if an [`Hsva`] color is translucent or not:
//!
//! ```
//! let red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 1.0);
//! let green = colo_rs::Hsva::new(120.0, 1.0, 1.0, 1.0);
//! let blue = colo_rs::Hsva::new(240.0, 1.0, 1.0, 1.0);
//! let black = colo_rs::Hsva::new(0.0, 0.0, 0.0, 1.0);
//! let white = colo_rs::Hsva::new(0.0, 0.0, 1.0, 1.0);
//! let translucent_gray = colo_rs::Hsva::new(0.0, 0.0, 0.5, 0.5);
//! let transparent = colo_rs::Hsva::default();
//!
//! assert!(!red.is_translucent());
//! assert!(!green.is_translucent());
//! assert!(!blue.is_translucent());
//! assert!(!black.is_translucent());
//! assert!(!white.is_translucent());
//! assert!(translucent_gray.is_translucent());
//! assert!(!transparent.is_translucent());
//! ```
//!
//! Check if an [`Hsva`] color is opaque or not:
//!
//! ```
//! let red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 1.0);
//! let green = colo_rs::Hsva::new(120.0, 1.0, 1.0, 1.0);
//! let blue = colo_rs::Hsva::new(240.0, 1.0, 1.0, 1.0);
//! let black = colo_rs::Hsva::new(0.0, 0.0, 0.0, 1.0);
//! let white = colo_rs::Hsva::new(0.0, 0.0, 1.0, 1.0);
//! let translucent_gray = colo_rs::Hsva::new(0.0, 0.0, 0.5, 0.5);
//! let transparent = colo_rs::Hsva::default();
//!
//! assert!(red.is_opaque());
//! assert!(green.is_opaque());
//! assert!(blue.is_opaque());
//! assert!(black.is_opaque());
//! assert!(white.is_opaque());
//! assert!(!translucent_gray.is_opaque());
//! assert!(!transparent.is_opaque());
//! ```

use std::{
    fmt::{Display, Formatter},
    hash::{Hash, Hasher},
    ops::{Range, RangeInclusive},
};

use crate::{Hsla, Rgba};

/// An HSVA color.
///
/// The `Hsva` color space is a commonly used color space in which the hue,
/// saturation, value, and alpha channels are used to represent a color. The hue
/// channel is the color's primary color, the saturation channel is the color's
/// intensity, and the value channel is the color's brightness.
///
/// - Hue must be an angle in the range \[0.0, 360.0\).
/// - Saturation must be a value in the range \[0.0, 1.0\].
/// - Value must be a value in the range \[0.0, 1.0\].
/// - Alpha must be a value in the range \[0.0, 1.0\].
///
/// # Examples
///
/// You can create a new `Hsva` color from individual hue, saturation, value,
/// and alpha values:
///
/// ```
/// let red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 1.0);
/// let green = colo_rs::Hsva::from([120.0, 1.0, 1.0]);
/// let blue = colo_rs::Hsva::from([240.0, 1.0, 1.0, 1.0]);
/// let black = colo_rs::Hsva::from((0.0, 0.0, 0.0));
/// let white = colo_rs::Hsva::from((0.0, 0.0, 1.0, 1.0));
/// ```
///
/// Or use the default transparent black color:
///
/// ```
/// let transparent = colo_rs::Hsva::default();
/// ```
///
/// Check if an `Hsva` color is transparent or not:
///
/// ```
/// let red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 1.0);
/// let green = colo_rs::Hsva::new(120.0, 1.0, 1.0, 1.0);
/// let blue = colo_rs::Hsva::new(240.0, 1.0, 1.0, 1.0);
/// let black = colo_rs::Hsva::new(0.0, 0.0, 0.0, 1.0);
/// let white = colo_rs::Hsva::new(0.0, 0.0, 1.0, 1.0);
/// let translucent_gray = colo_rs::Hsva::new(0.0, 0.0, 0.5, 0.5);
/// let transparent = colo_rs::Hsva::default();
///
/// assert!(!red.is_transparent());
/// assert!(!green.is_transparent());
/// assert!(!blue.is_transparent());
/// assert!(!black.is_transparent());
/// assert!(!white.is_transparent());
/// assert!(!translucent_gray.is_transparent());
/// assert!(transparent.is_transparent());
/// ```
///
/// Check if an `Hsva` color is translucent or not:
///
/// ```
/// let red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 1.0);
/// let green = colo_rs::Hsva::new(120.0, 1.0, 1.0, 1.0);
/// let blue = colo_rs::Hsva::new(240.0, 1.0, 1.0, 1.0);
/// let black = colo_rs::Hsva::new(0.0, 0.0, 0.0, 1.0);
/// let white = colo_rs::Hsva::new(0.0, 0.0, 1.0, 1.0);
/// let translucent_gray = colo_rs::Hsva::new(0.0, 0.0, 0.5, 0.5);
/// let transparent = colo_rs::Hsva::default();
///
/// assert!(!red.is_translucent());
/// assert!(!green.is_translucent());
/// assert!(!blue.is_translucent());
/// assert!(!black.is_translucent());
/// assert!(!white.is_translucent());
/// assert!(translucent_gray.is_translucent());
/// assert!(!transparent.is_translucent());
/// ```
///
/// Check if an `Hsva` color is opaque or not:
///
/// ```
/// let red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 1.0);
/// let green = colo_rs::Hsva::new(120.0, 1.0, 1.0, 1.0);
/// let blue = colo_rs::Hsva::new(240.0, 1.0, 1.0, 1.0);
/// let black = colo_rs::Hsva::new(0.0, 0.0, 0.0, 1.0);
/// let white = colo_rs::Hsva::new(0.0, 0.0, 1.0, 1.0);
/// let translucent_gray = colo_rs::Hsva::new(0.0, 0.0, 0.5, 0.5);
/// let transparent = colo_rs::Hsva::default();
///
/// assert!(red.is_opaque());
/// assert!(green.is_opaque());
/// assert!(blue.is_opaque());
/// assert!(black.is_opaque());
/// assert!(white.is_opaque());
/// assert!(!translucent_gray.is_opaque());
/// assert!(!transparent.is_opaque());
/// ```
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Hsva {
    /// The hue angle.
    h: f64,

    /// The saturation level.
    s: f64,

    /// The brightness value.
    v: f64,

    /// The alpha channel.
    a: f64,
}

impl Hsva {
    /// The minimum hue value.
    pub const HUE_MIN: f64 = 0.0f64;

    /// The maximum hue value.
    pub const HUE_MAX: f64 = 360.0f64;

    /// The hue range.
    pub const HUE_RANGE: Range<f64> = Self::HUE_MIN..Self::HUE_MAX;

    /// The angle of a sextant in the hue range.
    pub const HUE_SEXTANT: f64 = 60.0f64;

    /// The minimum value for saturation, brightness, and alpha channels.
    pub const CHANNEL_MIN: f64 = 0.0f64;

    /// The maximum value for saturation, brightness, and alpha channels.
    pub const CHANNEL_MAX: f64 = 1.0f64;

    /// The value range for saturation, brightness, and alpha channels.
    pub const CHANNEL_RANGE: RangeInclusive<f64> = Self::CHANNEL_MIN..=Self::CHANNEL_MAX;

    /// Creates a new `Hsva` color with the given h, s, v, and a values.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 1.0);
    /// let green = colo_rs::Hsva::new(120.0, 1.0, 1.0, 1.0);
    /// let blue = colo_rs::Hsva::new(240.0, 1.0, 1.0, 1.0);
    /// let black = colo_rs::Hsva::new(0.0, 0.0, 0.0, 1.0);
    /// let white = colo_rs::Hsva::new(0.0, 0.0, 1.0, 1.0);
    /// let translucent_gray = colo_rs::Hsva::new(0.0, 0.0, 0.5, 0.5);
    /// let transparent = colo_rs::Hsva::new(0.0, 0.0, 0.0, 0.0);
    /// ```
    #[inline]
    pub fn new(h: f64, s: f64, v: f64, a: f64) -> Self {
        let h = Self::cycle_hue(h);
        let s = Self::clamp_channel(s);
        let v = Self::clamp_channel(v);
        let a = Self::clamp_channel(a);

        Self { h, s, v, a }
    }

    /// Gets the hue angle value.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 1.0);
    /// assert_eq!(red.h(), 0.0);
    /// ```
    #[inline]
    pub const fn h(&self) -> f64 {
        self.h
    }

    /// Sets the hue angle value.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut red = colo_rs::Hsva::new(180.0, 1.0, 1.0, 1.0);
    /// red.set_h(0.0);
    /// assert_eq!(red.h(), 0.0);
    /// ```
    #[inline]
    pub fn set_h(&mut self, value: f64) {
        self.h = Self::cycle_hue(value);
    }

    /// Gets the saturation value.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 1.0);
    /// assert_eq!(red.s(), 1.0);
    /// ```
    #[inline]
    pub const fn s(&self) -> f64 {
        self.s
    }

    /// Sets the saturation value.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut red = colo_rs::Hsva::new(0.0, 0.0, 1.0, 1.0);
    /// red.set_s(1.0);
    /// assert_eq!(red.s(), 1.0);
    /// ```
    #[inline]
    pub fn set_s(&mut self, value: f64) {
        self.s = Self::clamp_channel(value);
    }

    /// Gets the brightness value.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 1.0);
    /// assert_eq!(red.v(), 1.0);
    /// ```
    #[inline]
    pub const fn v(&self) -> f64 {
        self.v
    }

    /// Sets the brightness value.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut red = colo_rs::Hsva::new(0.0, 1.0, 0.0, 1.0);
    /// red.set_v(1.0);
    /// assert_eq!(red.v(), 1.0);
    /// ```
    #[inline]
    pub fn set_v(&mut self, value: f64) {
        self.v = Self::clamp_channel(value);
    }

    /// Gets the alpha value.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 1.0);
    /// assert_eq!(red.a(), 1.0);
    /// ```
    #[inline]
    pub const fn a(&self) -> f64 {
        self.a
    }

    /// Sets the alpha value.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 0.0);
    /// red.set_a(1.0);
    /// assert_eq!(red.a(), 1.0);
    /// ```
    #[inline]
    pub fn set_a(&mut self, value: f64) {
        self.a = Self::clamp_channel(value);
    }

    /// Checks if the color is transparent.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 1.0);
    /// let green = colo_rs::Hsva::new(120.0, 1.0, 1.0, 1.0);
    /// let blue = colo_rs::Hsva::new(240.0, 1.0, 1.0, 1.0);
    /// let black = colo_rs::Hsva::new(0.0, 0.0, 0.0, 1.0);
    /// let white = colo_rs::Hsva::new(0.0, 0.0, 1.0, 1.0);
    /// let translucent_gray = colo_rs::Hsva::new(0.0, 0.0, 0.5, 0.5);
    /// let transparent = colo_rs::Hsva::default();
    ///
    /// assert!(!red.is_transparent());
    /// assert!(!green.is_transparent());
    /// assert!(!blue.is_transparent());
    /// assert!(!black.is_transparent());
    /// assert!(!white.is_transparent());
    /// assert!(!translucent_gray.is_transparent());
    /// assert!(transparent.is_transparent());
    /// ```
    #[inline]
    pub fn is_transparent(&self) -> bool {
        self.a() == Self::CHANNEL_MIN
    }

    /// Checks if the color is translucent.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 1.0);
    /// let green = colo_rs::Hsva::new(120.0, 1.0, 1.0, 1.0);
    /// let blue = colo_rs::Hsva::new(240.0, 1.0, 1.0, 1.0);
    /// let black = colo_rs::Hsva::new(0.0, 0.0, 0.0, 1.0);
    /// let white = colo_rs::Hsva::new(0.0, 0.0, 1.0, 1.0);
    /// let translucent_gray = colo_rs::Hsva::new(0.0, 0.0, 0.5, 0.5);
    /// let transparent = colo_rs::Hsva::default();
    ///
    /// assert!(!red.is_translucent());
    /// assert!(!green.is_translucent());
    /// assert!(!blue.is_translucent());
    /// assert!(!black.is_translucent());
    /// assert!(!white.is_translucent());
    /// assert!(translucent_gray.is_translucent());
    /// assert!(!transparent.is_translucent());
    /// ```
    #[inline]
    pub fn is_translucent(&self) -> bool {
        self.a() > Self::CHANNEL_MIN && self.a() < Self::CHANNEL_MAX
    }

    /// Checks if the color is opaque.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Hsva::new(0.0, 1.0, 1.0, 1.0);
    /// let green = colo_rs::Hsva::new(120.0, 1.0, 1.0, 1.0);
    /// let blue = colo_rs::Hsva::new(240.0, 1.0, 1.0, 1.0);
    /// let black = colo_rs::Hsva::new(0.0, 0.0, 0.0, 1.0);
    /// let white = colo_rs::Hsva::new(0.0, 0.0, 1.0, 1.0);
    /// let translucent_gray = colo_rs::Hsva::new(0.0, 0.0, 0.5, 0.5);
    /// let transparent = colo_rs::Hsva::default();
    ///
    /// assert!(red.is_opaque());
    /// assert!(green.is_opaque());
    /// assert!(blue.is_opaque());
    /// assert!(black.is_opaque());
    /// assert!(white.is_opaque());
    /// assert!(!translucent_gray.is_opaque());
    /// assert!(!transparent.is_opaque());
    /// ```
    #[inline]
    pub fn is_opaque(&self) -> bool {
        self.a() == Self::CHANNEL_MAX
    }

    /// Cycle the hue value into the range \[0.0, 360.0\).
    #[inline]
    fn cycle_hue(hue: f64) -> f64 {
        hue.rem_euclid(Self::HUE_MAX) % Self::HUE_MAX
    }

    /// Clamp the channel value into the range \[0.0, 1.0\].
    #[inline]
    fn clamp_channel(channel: f64) -> f64 {
        channel.clamp(Self::CHANNEL_MIN, Self::CHANNEL_MAX)
    }
}

impl Eq for Hsva {}

impl Display for Hsva {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Rgba::from(*self).fmt(f)
    }
}

impl Hash for Hsva {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Rgba::from(*self).hash(state);
    }
}

impl From<(f64, f64, f64, f64)> for Hsva {
    #[inline]
    fn from((h, s, v, a): (f64, f64, f64, f64)) -> Self {
        Self::new(h, s, v, a)
    }
}

impl From<Hsva> for (f64, f64, f64, f64) {
    #[inline]
    fn from(hsva: Hsva) -> Self {
        (hsva.h(), hsva.s(), hsva.v(), hsva.a())
    }
}

impl From<(f64, f64, f64)> for Hsva {
    #[inline]
    fn from((h, s, v): (f64, f64, f64)) -> Self {
        Self::new(h, s, v, Self::CHANNEL_MAX)
    }
}

impl From<Hsva> for (f64, f64, f64) {
    #[inline]
    fn from(hsva: Hsva) -> Self {
        (hsva.h(), hsva.s(), hsva.v())
    }
}

impl From<[f64; 4]> for Hsva {
    #[inline]
    fn from([h, s, v, a]: [f64; 4]) -> Self {
        Self::from((h, s, v, a))
    }
}

impl From<Hsva> for [f64; 4] {
    #[inline]
    fn from(hsva: Hsva) -> Self {
        [hsva.h(), hsva.s(), hsva.v(), hsva.a()]
    }
}

impl From<[f64; 3]> for Hsva {
    #[inline]
    fn from([h, s, v]: [f64; 3]) -> Self {
        Self::from((h, s, v))
    }
}

impl From<Hsva> for [f64; 3] {
    #[inline]
    fn from(hsva: Hsva) -> Self {
        [hsva.h(), hsva.s(), hsva.v()]
    }
}

impl From<Rgba> for Hsva {
    fn from(rgba: Rgba) -> Self {
        let (r, g, b, a): (f64, f64, f64, f64) = rgba.into();

        let max = r.max(g).max(b);
        let min = r.min(g).min(b);
        let delta = max - min;

        let v = max;
        let s = if max == Rgba::NORM_CHANNEL_MIN {
            Self::CHANNEL_MIN
        } else {
            delta / max
        };

        let h = if delta == Rgba::NORM_CHANNEL_MIN {
            Self::CHANNEL_MIN
        } else if max == r {
            Self::HUE_SEXTANT * (((g - b) / delta) % 6.0)
        } else if max == g {
            Self::HUE_SEXTANT * (((b - r) / delta) + 2.0)
        } else if max == b {
            Self::HUE_SEXTANT * (((r - g) / delta) + 4.0)
        } else {
            unreachable!("max(r, g, b) must be at least one of r, g, or b");
        };

        Self::new(h, s, v, a)
    }
}

impl From<Hsla> for Hsva {
    fn from(hsla: Hsla) -> Self {
        let (h, s, l, a) = hsla.into();

        let l = l * 2.0;
        let num = if l <= Hsla::CHANNEL_MAX { l } else { 2.0 - l };

        let s = s * num;
        let c = l + s;
        let v = c / 2.0;
        let s = if c == Hsla::CHANNEL_MIN {
            Self::CHANNEL_MIN
        } else {
            s * 2.0 / c
        };

        Self::new(h, s, v, a)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hsva_new() {
        let transparent = Hsva::default();

        let white = Hsva::new(0.0, 0.0, 1.0, 1.0);
        let transparent_black = Hsva::new(0.0, 0.0, 0.0, 0.0);

        assert_ne!(white, transparent);
        assert_eq!(transparent_black, transparent);
    }

    #[test]
    fn test_hsva_is_transparent() {
        let transparent = Hsva::default();
        let translucent_gray = Hsva::new(0.0, 0.0, 0.5, 0.5);
        let white = Hsva::new(0.0, 0.0, 1.0, 1.0);

        assert!(transparent.is_transparent());
        assert!(!translucent_gray.is_transparent());
        assert!(!white.is_transparent());
    }

    #[test]
    fn test_hsva_is_translucent() {
        let transparent = Hsva::default();
        let translucent_gray = Hsva::new(0.0, 0.0, 0.5, 0.5);
        let white = Hsva::new(0.0, 0.0, 1.0, 1.0);

        assert!(!transparent.is_translucent());
        assert!(translucent_gray.is_translucent());
        assert!(!white.is_translucent());
    }

    #[test]
    fn test_hsva_is_opaque() {
        let transparent = Hsva::default();
        let translucent_gray = Hsva::new(0.0, 0.0, 0.5, 0.5);
        let white = Hsva::new(0.0, 0.0, 1.0, 1.0);

        assert!(transparent.is_transparent());
        assert!(!translucent_gray.is_transparent());
        assert!(!white.is_transparent());
    }

    #[test]
    fn test_hsva_from_rgba() {
        let black_rgba = Rgba::new(0, 0, 0, 255);
        let black_hsva = Hsva::new(0.0, 0.0, 0.0, 1.0);

        let translucent_gray_rgba = Rgba::new(128, 128, 128, 128);
        let translucent_gray_hsva = Hsva::new(0.0, 0.0, 0.5019607843137255, 0.5019607843137255);

        assert_eq!(black_hsva, Hsva::from(black_rgba));
        assert_eq!(translucent_gray_hsva, Hsva::from(translucent_gray_rgba));
    }

    #[test]
    fn test_hsva_from_hsla() {
        let black_hsla = Hsla::new(0.0, 0.0, 0.0, 1.0);
        let black_hsva = Hsva::new(0.0, 0.0, 0.0, 1.0);

        let translucent_gray_hsla = Hsla::new(0.0, 0.0, 0.5, 0.5);
        let translucent_gray_hsva = Hsva::new(0.0, 0.0, 0.5, 0.5);

        assert_eq!(black_hsva, Hsva::from(black_hsla));
        assert_eq!(translucent_gray_hsva, Hsva::from(translucent_gray_hsla));
    }
}
