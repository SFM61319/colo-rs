//! An HSLA color.
//!
//! This module contains the [`Hsla`] color space type, and several error types
//! that may result from working with [`Hsla`] colors.
//!
//! # Examples
//!
//! You can create a new [`Hsla`] color from individual hue, saturation,
//! lightness, and alpha values:
//!
//! ```
//! let red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 1.0);
//! let green = colo_rs::Hsla::from([120.0, 1.0, 0.5]);
//! let blue = colo_rs::Hsla::from([240.0, 1.0, 0.5, 1.0]);
//! let black = colo_rs::Hsla::from((0.0, 0.0, 0.0));
//! let white = colo_rs::Hsla::from((0.0, 0.0, 1.0, 1.0));
//! ```
//!
//! Or use the default transparent black color:
//!
//! ```
//! let transparent = colo_rs::Hsla::default();
//! ```
//!
//! Check if an [`Hsla`] color is transparent or not:
//!
//! ```
//! let red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 1.0);
//! let green = colo_rs::Hsla::new(120.0, 1.0, 0.5, 1.0);
//! let blue = colo_rs::Hsla::new(240.0, 1.0, 0.5, 1.0);
//! let black = colo_rs::Hsla::new(0.0, 0.0, 0.0, 1.0);
//! let white = colo_rs::Hsla::new(0.0, 0.0, 1.0, 1.0);
//! let translucent_gray = colo_rs::Hsla::new(0.0, 0.0, 0.5, 0.5);
//! let transparent = colo_rs::Hsla::default();
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
//! Check if an [`Hsla`] color is translucent or not:
//!
//! ```
//! let red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 1.0);
//! let green = colo_rs::Hsla::new(120.0, 1.0, 0.5, 1.0);
//! let blue = colo_rs::Hsla::new(240.0, 1.0, 0.5, 1.0);
//! let black = colo_rs::Hsla::new(0.0, 0.0, 0.0, 1.0);
//! let white = colo_rs::Hsla::new(0.0, 0.0, 1.0, 1.0);
//! let translucent_gray = colo_rs::Hsla::new(0.0, 0.0, 0.5, 0.5);
//! let transparent = colo_rs::Hsla::default();
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
//! Check if an [`Hsla`] color is opaque or not:
//!
//! ```
//! let red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 1.0);
//! let green = colo_rs::Hsla::new(120.0, 1.0, 0.5, 1.0);
//! let blue = colo_rs::Hsla::new(240.0, 1.0, 0.5, 1.0);
//! let black = colo_rs::Hsla::new(0.0, 0.0, 0.0, 1.0);
//! let white = colo_rs::Hsla::new(0.0, 0.0, 1.0, 1.0);
//! let translucent_gray = colo_rs::Hsla::new(0.0, 0.0, 0.5, 0.5);
//! let transparent = colo_rs::Hsla::default();
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

use crate::{Hsva, Rgba};

/// An HSLA color.
///
/// The `Hsla` color space is a commonly used color space in which the hue,
/// saturation, lightness, and alpha channels are used to represent a color.
/// The hue channel is the color's primary color, the saturation channel is the
/// color's intensity, and the lightness channel is the color's lightness.
///
/// - Hue must be an angle in the range \[0.0, 360.0\).
/// - Saturation must be a value in the range \[0.0, 1.0\].
/// - Lightness must be a value in the range \[0.0, 1.0\].
/// - Alpha must be a value in the range \[0.0, 1.0\].
///
/// # Examples
///
/// You can create a new `Hsla` color from individual hue, saturation,
/// lightness, and alpha values:
///
/// ```
/// let red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 1.0);
/// let green = colo_rs::Hsla::from([120.0, 1.0, 0.5]);
/// let blue = colo_rs::Hsla::from([240.0, 1.0, 0.5, 1.0]);
/// let black = colo_rs::Hsla::from((0.0, 0.0, 0.0));
/// let white = colo_rs::Hsla::from((0.0, 0.0, 1.0, 1.0));
/// ```
///
/// Or use the default transparent black color:
///
/// ```
/// let transparent = colo_rs::Hsla::default();
/// ```
///
/// Check if an `Hsla` color is transparent or not:
///
/// ```
/// let red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 1.0);
/// let green = colo_rs::Hsla::new(120.0, 1.0, 0.5, 1.0);
/// let blue = colo_rs::Hsla::new(240.0, 1.0, 0.5, 1.0);
/// let black = colo_rs::Hsla::new(0.0, 0.0, 0.0, 1.0);
/// let white = colo_rs::Hsla::new(0.0, 0.0, 1.0, 1.0);
/// let translucent_gray = colo_rs::Hsla::new(0.0, 0.0, 0.5, 0.5);
/// let transparent = colo_rs::Hsla::default();
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
/// Check if an `Hsla` color is translucent or not:
///
/// ```
/// let red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 1.0);
/// let green = colo_rs::Hsla::new(120.0, 1.0, 0.5, 1.0);
/// let blue = colo_rs::Hsla::new(240.0, 1.0, 0.5, 1.0);
/// let black = colo_rs::Hsla::new(0.0, 0.0, 0.0, 1.0);
/// let white = colo_rs::Hsla::new(0.0, 0.0, 1.0, 1.0);
/// let translucent_gray = colo_rs::Hsla::new(0.0, 0.0, 0.5, 0.5);
/// let transparent = colo_rs::Hsla::default();
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
/// Check if an `Hsla` color is opaque or not:
///
/// ```
/// let red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 1.0);
/// let green = colo_rs::Hsla::new(120.0, 1.0, 0.5, 1.0);
/// let blue = colo_rs::Hsla::new(240.0, 1.0, 0.5, 1.0);
/// let black = colo_rs::Hsla::new(0.0, 0.0, 0.0, 1.0);
/// let white = colo_rs::Hsla::new(0.0, 0.0, 1.0, 1.0);
/// let translucent_gray = colo_rs::Hsla::new(0.0, 0.0, 0.5, 0.5);
/// let transparent = colo_rs::Hsla::default();
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
pub struct Hsla {
    /// The hue angle.
    h: f64,

    /// The saturation level.
    s: f64,

    /// The lightness value.
    l: f64,

    /// The alpha channel.
    a: f64,
}

impl Hsla {
    /// The minimum hue value.
    pub const HUE_MIN: f64 = 0.0f64;

    /// The maximum hue value.
    pub const HUE_MAX: f64 = 360.0f64;

    /// The hue range.
    pub const HUE_RANGE: Range<f64> = Self::HUE_MIN..Self::HUE_MAX;

    /// The angle of a sextant in the hue range.
    pub const HUE_SEXTANT: f64 = 60.0f64;

    /// The minimum value for saturation, lightness, and alpha channels.
    pub const CHANNEL_MIN: f64 = 0.0f64;

    /// The maximum value for saturation, lightness, and alpha channels.
    pub const CHANNEL_MAX: f64 = 1.0f64;

    /// The value range for saturation, lightness, and alpha channels.
    pub const CHANNEL_RANGE: RangeInclusive<f64> = Self::CHANNEL_MIN..=Self::CHANNEL_MAX;

    /// Creates a new `Hsla` color with the given h, s, l, and a values.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 1.0);
    /// let green = colo_rs::Hsla::new(120.0, 1.0, 0.5, 1.0);
    /// let blue = colo_rs::Hsla::new(240.0, 1.0, 0.5, 1.0);
    /// let black = colo_rs::Hsla::new(0.0, 0.0, 0.0, 1.0);
    /// let white = colo_rs::Hsla::new(0.0, 0.0, 1.0, 1.0);
    /// let translucent_gray = colo_rs::Hsla::new(0.0, 0.0, 0.5, 0.5);
    /// let transparent = colo_rs::Hsla::new(0.0, 0.0, 0.0, 0.0);
    /// ```
    #[inline]
    pub fn new(h: f64, s: f64, l: f64, a: f64) -> Self {
        let h = Self::cycle_hue(h);
        let s = Self::clamp_channel(s);
        let l = Self::clamp_channel(l);
        let a = Self::clamp_channel(a);

        Self { h, s, l, a }
    }

    /// Gets the hue angle value.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 1.0);
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
    /// let mut red = colo_rs::Hsla::new(180.0, 1.0, 0.5, 1.0);
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
    /// let red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 1.0);
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
    /// let mut red = colo_rs::Hsla::new(0.0, 0.0, 0.5, 1.0);
    /// red.set_s(1.0);
    /// assert_eq!(red.s(), 1.0);
    /// ```
    #[inline]
    pub fn set_s(&mut self, value: f64) {
        self.s = Self::clamp_channel(value);
    }

    /// Gets the lightness value.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 1.0);
    /// assert_eq!(red.l(), 0.5);
    /// ```
    #[inline]
    pub const fn l(&self) -> f64 {
        self.l
    }

    /// Sets the lightness value.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut red = colo_rs::Hsla::new(0.0, 1.0, 1.0, 1.0);
    /// red.set_l(0.5);
    /// assert_eq!(red.l(), 0.5);
    /// ```
    #[inline]
    pub fn set_l(&mut self, value: f64) {
        self.l = Self::clamp_channel(value);
    }

    /// Gets the alpha value.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 1.0);
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
    /// let mut red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 0.0);
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
    /// let red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 1.0);
    /// let green = colo_rs::Hsla::new(120.0, 1.0, 0.5, 1.0);
    /// let blue = colo_rs::Hsla::new(240.0, 1.0, 0.5, 1.0);
    /// let black = colo_rs::Hsla::new(0.0, 0.0, 0.0, 1.0);
    /// let white = colo_rs::Hsla::new(0.0, 0.0, 1.0, 1.0);
    /// let translucent_gray = colo_rs::Hsla::new(0.0, 0.0, 0.5, 0.5);
    /// let transparent = colo_rs::Hsla::default();
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
    /// let red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 1.0);
    /// let green = colo_rs::Hsla::new(120.0, 1.0, 0.5, 1.0);
    /// let blue = colo_rs::Hsla::new(240.0, 1.0, 0.5, 1.0);
    /// let black = colo_rs::Hsla::new(0.0, 0.0, 0.0, 1.0);
    /// let white = colo_rs::Hsla::new(0.0, 0.0, 1.0, 1.0);
    /// let translucent_gray = colo_rs::Hsla::new(0.0, 0.0, 0.5, 0.5);
    /// let transparent = colo_rs::Hsla::default();
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
    /// let red = colo_rs::Hsla::new(0.0, 1.0, 0.5, 1.0);
    /// let green = colo_rs::Hsla::new(120.0, 1.0, 0.5, 1.0);
    /// let blue = colo_rs::Hsla::new(240.0, 1.0, 0.5, 1.0);
    /// let black = colo_rs::Hsla::new(0.0, 0.0, 0.0, 1.0);
    /// let white = colo_rs::Hsla::new(0.0, 0.0, 1.0, 1.0);
    /// let translucent_gray = colo_rs::Hsla::new(0.0, 0.0, 0.5, 0.5);
    /// let transparent = colo_rs::Hsla::default();
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

impl Eq for Hsla {}

impl Display for Hsla {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Rgba::from(*self).fmt(f)
    }
}

impl Hash for Hsla {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Rgba::from(*self).hash(state);
    }
}

impl From<(f64, f64, f64, f64)> for Hsla {
    #[inline]
    fn from((h, s, l, a): (f64, f64, f64, f64)) -> Self {
        Self::new(h, s, l, a)
    }
}

impl From<Hsla> for (f64, f64, f64, f64) {
    #[inline]
    fn from(hsla: Hsla) -> Self {
        (hsla.h(), hsla.s(), hsla.l(), hsla.a())
    }
}

impl From<(f64, f64, f64)> for Hsla {
    #[inline]
    fn from((h, s, l): (f64, f64, f64)) -> Self {
        Self::new(h, s, l, Self::CHANNEL_MAX)
    }
}

impl From<Hsla> for (f64, f64, f64) {
    #[inline]
    fn from(hsla: Hsla) -> Self {
        (hsla.h(), hsla.s(), hsla.l())
    }
}

impl From<[f64; 4]> for Hsla {
    #[inline]
    fn from([h, s, l, a]: [f64; 4]) -> Self {
        Self::from((h, s, l, a))
    }
}

impl From<Hsla> for [f64; 4] {
    #[inline]
    fn from(hsla: Hsla) -> Self {
        [hsla.h(), hsla.s(), hsla.l(), hsla.a()]
    }
}

impl From<[f64; 3]> for Hsla {
    #[inline]
    fn from([h, s, l]: [f64; 3]) -> Self {
        Self::from((h, s, l))
    }
}

impl From<Hsla> for [f64; 3] {
    #[inline]
    fn from(hsla: Hsla) -> Self {
        [hsla.h(), hsla.s(), hsla.l()]
    }
}

impl From<Rgba> for Hsla {
    fn from(rgba: Rgba) -> Self {
        use std::ops::{Mul, Neg, Sub};

        let (r, g, b, a): (f64, f64, f64, f64) = rgba.into();

        let max = r.max(g).max(b);
        let min = r.min(g).min(b);
        let delta = max - min;

        let l = (max + min) / 2.0;
        let s = if delta == Rgba::NORM_CHANNEL_MIN {
            Self::CHANNEL_MIN
        } else {
            let denom = l
                .mul(2.0)
                .sub(Self::CHANNEL_MAX)
                .abs()
                .sub(Self::CHANNEL_MAX)
                .neg();
            delta / denom
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

        Self::new(h, s, l, a)
    }
}

impl From<Hsva> for Hsla {
    fn from(hsva: Hsva) -> Self {
        let (h, s, v, a) = hsva.into();

        let l = v * (2.0 - s);
        let denom = if l <= Self::CHANNEL_MAX { l } else { 2.0 - l };

        let l = l / 2.0;
        let s = if denom == Hsva::CHANNEL_MIN {
            Self::CHANNEL_MIN
        } else {
            s * v / denom
        };

        Self::new(h, s, l, a)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hsla_new() {
        let transparent = Hsla::default();

        let white = Hsla::new(0.0, 0.0, 1.0, 1.0);
        let transparent_black = Hsla::new(0.0, 0.0, 0.0, 0.0);

        assert_ne!(white, transparent);
        assert_eq!(transparent_black, transparent);
    }

    #[test]
    fn test_hsla_is_transparent() {
        let transparent = Hsla::default();
        let translucent_gray = Hsla::new(0.0, 0.0, 0.5, 0.5);
        let white = Hsla::new(0.0, 0.0, 1.0, 1.0);

        assert!(transparent.is_transparent());
        assert!(!translucent_gray.is_transparent());
        assert!(!white.is_transparent());
    }

    #[test]
    fn test_hsla_is_translucent() {
        let transparent = Hsla::default();
        let translucent_gray = Hsla::new(0.0, 0.0, 0.5, 0.5);
        let white = Hsla::new(0.0, 0.0, 1.0, 1.0);

        assert!(!transparent.is_translucent());
        assert!(translucent_gray.is_translucent());
        assert!(!white.is_translucent());
    }

    #[test]
    fn test_hsla_is_opaque() {
        let transparent = Hsla::default();
        let translucent_gray = Hsla::new(0.0, 0.0, 0.5, 0.5);
        let white = Hsla::new(0.0, 0.0, 1.0, 1.0);

        assert!(transparent.is_transparent());
        assert!(!translucent_gray.is_transparent());
        assert!(!white.is_transparent());
    }

    #[test]
    fn test_hsla_from_rgba() {
        let black_rgba = Rgba::new(0, 0, 0, 255);
        let black_hsla = Hsla::new(0.0, 0.0, 0.0, 1.0);

        let translucent_gray_rgba = Rgba::new(128, 128, 128, 128);
        let translucent_gray_hsla = Hsla::new(0.0, 0.0, 0.5019607843137255, 0.5019607843137255);

        assert_eq!(black_hsla, Hsla::from(black_rgba));
        assert_eq!(translucent_gray_hsla, Hsla::from(translucent_gray_rgba));
    }

    #[test]
    fn test_hsla_from_hsva() {
        let black_hsva = Hsva::new(0.0, 0.0, 0.0, 1.0);
        let black_hsla = Hsla::new(0.0, 0.0, 0.0, 1.0);

        let translucent_gray_hsva = Hsva::new(0.0, 0.0, 0.5, 0.5);
        let translucent_gray_hsla = Hsla::new(0.0, 0.0, 0.5, 0.5);

        assert_eq!(black_hsla, Hsla::from(black_hsva));
        assert_eq!(translucent_gray_hsla, Hsla::from(translucent_gray_hsva));
    }
}
